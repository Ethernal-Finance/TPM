
// File: THE_PROMISED_MOON3/contracts/Libraries/IDividendDistributor.sol


pragma solidity ^0.8.0;

interface IDividendDistributor {
    function setDistributionCriteria(uint256 _minPeriod, uint256 _minDistribution) external;
    function setShare(address shareholder, uint256 amount) external;
    function deposit() external payable;
    function process(uint256 gas) external;
    function changeTokenReward(address newTokenDividends) external;
    function changeRouter(address _router) external;
    function unstuckToken(address _receiver) external;
}
// File: THE_PROMISED_MOON3/contracts/Libraries/IFactory.sol


pragma solidity ^0.8.0;

interface IFactory {
    function getPair(address token0, address token1) external view returns (address _pair);  
    function createPair(address token0, address token1) external returns (address _pair);
}

// File: THE_PROMISED_MOON3/contracts/Libraries/ILiqPair.sol


pragma solidity ^0.8.0;

interface ILiqPair {
    function getReserves() external view returns (uint112 _reserve0, uint112 _reserve1, uint32 _blockTimestampLast);
    function token0() external view returns(address _adr);
    function token1() external view returns(address _adr);    
}
// File: THE_PROMISED_MOON3/contracts/Libraries/IDEXRouter.sol


pragma solidity ^0.8.0;

interface IDEXRouter {
    function factory() external pure returns (address);
    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint amountADesired,
        uint amountBDesired,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB, uint liquidity);

    function addLiquidityETH(
        address token,
        uint amountTokenDesired,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external payable returns (uint amountToken, uint amountETH, uint liquidity);

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;

    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external payable;

    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;

    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountETH);
}
// File: THE_PROMISED_MOON3/contracts/openzeppelin-contracts/token/ERC20/IERC20.sol


// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC20/IERC20.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
}

// File: THE_PROMISED_MOON3/contracts/openzeppelin-contracts/token/ERC20/extensions/IERC20Metadata.sol


// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/IERC20Metadata.sol)

pragma solidity ^0.8.0;


/**
 * @dev Interface for the optional metadata functions from the ERC20 standard.
 *
 * _Available since v4.1._
 */
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}

// File: THE_PROMISED_MOON3/contracts/openzeppelin-contracts/utils/Context.sol


// OpenZeppelin Contracts v4.4.1 (utils/Context.sol)

pragma solidity ^0.8.0;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

// File: THE_PROMISED_MOON3/contracts/Libraries/ERC20_2.sol


pragma solidity ^0.8.0;




contract ERC20_2 is Context, IERC20, IERC20Metadata {
    mapping(address => uint256) private _balances;

    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;

    /**
     * @dev Sets the values for {name} and {symbol}.
     *
     * All two of these values are immutable: they can only be set once during
     * construction.
     */
    constructor(string memory name_, string memory symbol_) {
        _name = name_;
        _symbol = symbol_;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view virtual override returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5.05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the default value returned by this function, unless
     * it's overridden.
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view virtual override returns (uint8) {
        return 18;
    }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(address account) public view virtual override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(address to, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _transfer(owner, to, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(address owner, address spender) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * NOTE: If `amount` is the maximum `uint256`, the allowance is not updated on
     * `transferFrom`. This is semantically equivalent to an infinite approval.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(address spender, uint256 amount) public virtual override returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20}.
     *
     * NOTE: Does not update the allowance if the current allowance
     * is the maximum `uint256`.
     *
     * Requirements:
     *
     * - `from` and `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     * - the caller must have allowance for ``from``'s tokens of at least
     * `amount`.
     */
    function transferFrom(address from, address to, uint256 amount) public virtual override returns (bool) {
        address spender = _msgSender();
        _spendAllowance(from, spender, amount);
        _transfer(from, to, amount);
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, allowance(owner, spender) + addedValue);
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        address owner = _msgSender();
        uint256 currentAllowance = allowance(owner, spender);
        require(currentAllowance >= subtractedValue, "ERC20: decreased allowance below zero");
        unchecked {
            _approve(owner, spender, currentAllowance - subtractedValue);
        }

        return true;
    }

    function _addBalance(address adr, uint256 amount) internal { _balances[adr] += amount; }

    function _subBalance(address adr, uint256 amount) internal { _balances[adr] -= amount; }

    /**
     * @dev Moves `amount` of tokens from `from` to `to`.
     *
     * This internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     */
    function _transfer(address from, address to, uint256 amount) internal virtual {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(from, to, amount);

        uint256 fromBalance = _balances[from];
        require(fromBalance >= amount, "ERC20: transfer amount exceeds balance");
        unchecked {
            _balances[from] = fromBalance - amount;
            // Overflow not possible: the sum of all balances is capped by totalSupply, and the sum is preserved by
            // decrementing then incrementing.
            _balances[to] += amount;
        }

        emit Transfer(from, to, amount);

        _afterTokenTransfer(from, to, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply += amount;
        unchecked {
            // Overflow not possible: balance + amount is at most totalSupply + amount, which is checked above.
            _balances[account] += amount;
        }
        emit Transfer(address(0), account, amount);

        _afterTokenTransfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        uint256 accountBalance = _balances[account];
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
        unchecked {
            _balances[account] = accountBalance - amount;
            // Overflow not possible: amount <= accountBalance <= totalSupply.
            _totalSupply -= amount;
        }

        emit Transfer(account, address(0), amount);
    }

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner` s tokens.
     *
     * This internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(address owner, address spender, uint256 amount) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Updates `owner` s allowance for `spender` based on spent `amount`.
     *
     * Does not update the allowance amount in case of infinite allowance.
     * Revert if not enough allowance is available.
     *
     * Might emit an {Approval} event.
     */
    function _spendAllowance(address owner, address spender, uint256 amount) internal virtual {
        uint256 currentAllowance = allowance(owner, spender);
        if (currentAllowance != type(uint256).max) {
            require(currentAllowance >= amount, "ERC20: insufficient allowance");
            unchecked {
                _approve(owner, spender, currentAllowance - amount);
            }
        }
    }

    /**
     * @dev Hook that is called before any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * will be transferred to `to`.
     * - when `from` is zero, `amount` tokens will be minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens will be burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(address from, address to, uint256 amount) internal virtual {}

    /**
     * @dev Hook that is called after any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * has been transferred to `to`.
     * - when `from` is zero, `amount` tokens have been minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens have been burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _afterTokenTransfer(address from, address to, uint256 amount) internal virtual {}
}

// File: THE_PROMISED_MOON3/contracts/openzeppelin-contracts/access/Ownable.sol


// OpenZeppelin Contracts (last updated v4.7.0) (access/Ownable.sol)

pragma solidity ^0.8.0;


/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby disabling any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

// File: THE_PROMISED_MOON3/contracts/openzeppelin-contracts/utils/math/SafeMath.sol


// OpenZeppelin Contracts (last updated v4.6.0) (utils/math/SafeMath.sol)

pragma solidity ^0.8.0;

// CAUTION
// This version of SafeMath should only be used with Solidity 0.8 or later,
// because it relies on the compiler's built in overflow checks.

/**
 * @dev Wrappers over Solidity's arithmetic operations.
 *
 * NOTE: `SafeMath` is generally not needed starting with Solidity 0.8, since the compiler
 * now has built in overflow checking.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            uint256 c = a + b;
            if (c < a) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b > a) return (false, 0);
            return (true, a - b);
        }
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
            // benefit is lost if 'b' is also tested.
            // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
            if (a == 0) return (true, 0);
            uint256 c = a * b;
            if (c / a != b) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a / b);
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a % b);
        }
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator.
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        unchecked {
            require(b <= a, errorMessage);
            return a - b;
        }
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a / b;
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a % b;
        }
    }
}

// File: THE_PROMISED_MOON3/contracts/Libraries/DividendDistributor.sol


pragma solidity ^0.8.0;





contract DividendDistributor is IDividendDistributor {
    using SafeMath for uint256;

    address _token;

    struct Share {
        uint256 amount;
        uint256 totalExcluded;
        uint256 totalRealised;
        uint256 lastReset;
    }

    // EARN
    IERC20 public RWRD = IERC20(0x0000000000000000000000000000000000000000);
    address WBNB = 0x0000000000000000000000000000000000000000;
    IDEXRouter router;

    address[] shareholders;
    mapping (address => uint256) shareholderIndexes;
    mapping (address => uint256) shareholderClaims;

    mapping (address => Share) public shares;

    uint256 public totalShares;
    uint256 public totalDividends;
    uint256 public totalDistributed;
    uint256 public dividendsPerShare;
    uint256 public dividendsPerShareAccuracyFactor = 10 ** 36;

    uint256 public minPeriod = 30 * 60;
    uint256 public minDistribution = 1 * (10 ** 12);
    uint256 public lastReset;

    uint256 currentIndex;

    bool initialized;
    modifier initialization() {
        require(!initialized);
        _;
        initialized = true;
    }

    modifier onlyToken() {
        require(msg.sender == _token); _;
    }

    constructor (address _router, address _WBNB) {
        WBNB = _WBNB;
        router = _router != address(0)
            ? IDEXRouter(_router)
            : IDEXRouter(0x10ED43C718714eb63d5aA57B78B54704E256024E);
        _token = msg.sender;
    }

    function setDistributionCriteria(uint256 _minPeriod, uint256 _minDistribution) external override onlyToken {
        minPeriod = _minPeriod;
        minDistribution = _minDistribution;
    }

    function setShare(address shareholder, uint256 amount) external override onlyToken {
        if(shares[shareholder].amount > 0){
            distributeDividend(shareholder);
        }

        if(amount > 0 && shares[shareholder].amount == 0){
            addShareholder(shareholder);
        }else if(amount == 0 && shares[shareholder].amount > 0){
            removeShareholder(shareholder);
        }

        totalShares = totalShares.sub(shares[shareholder].amount).add(amount);
        shares[shareholder].amount = amount;
        shares[shareholder].totalExcluded = getCumulativeDividends(shares[shareholder].amount);
    }

    function deposit() external payable override onlyToken {
        uint256 balanceBefore = RWRD.balanceOf(address(this));

        address[] memory path = new address[](2);
        path[0] = WBNB;
        path[1] = address(RWRD);

        router.swapExactETHForTokensSupportingFeeOnTransferTokens{value: msg.value}(
            0,
            path,
            address(this),
            block.timestamp
        );

        uint256 amount = RWRD.balanceOf(address(this)).sub(balanceBefore);

        totalDividends = totalDividends.add(amount);
        dividendsPerShare = dividendsPerShare.add(dividendsPerShareAccuracyFactor.mul(amount).div(totalShares));
    }

    function process(uint256 gas) external override onlyToken {
        uint256 shareholderCount = shareholders.length;

        if(shareholderCount == 0) { return; }

        uint256 gasUsed = 0;
        uint256 gasLeft = gasleft();

        uint256 iterations = 0;

        while(gasUsed < gas && iterations < shareholderCount) {
            if(currentIndex >= shareholderCount){
                currentIndex = 0;
            }

            if(shouldDistribute(shareholders[currentIndex])){
                distributeDividend(shareholders[currentIndex]);
            }

            gasUsed = gasUsed.add(gasLeft.sub(gasleft()));
            gasLeft = gasleft();
            currentIndex++;
            iterations++;
        }
    }
    
    function shouldDistribute(address shareholder) internal view returns (bool) {
        return shareholderClaims[shareholder] + minPeriod < block.timestamp
                && getUnpaidEarnings(shareholder) > minDistribution;
    }

    function distributeDividend(address shareholder) internal {
        if(shares[shareholder].amount == 0){ return; }

        if(shares[shareholder].lastReset != lastReset) {
            shares[shareholder].lastReset = lastReset;
            shares[shareholder].totalRealised = 0;
            shares[shareholder].totalExcluded = 0;
        }

        uint256 amount = getUnpaidEarnings(shareholder);
        if(amount > 0){
            totalDistributed = totalDistributed.add(amount);
            RWRD.transfer(shareholder, amount);
            shareholderClaims[shareholder] = block.timestamp;
            shares[shareholder].totalRealised = shares[shareholder].totalRealised.add(amount);
            shares[shareholder].totalExcluded = getCumulativeDividends(shares[shareholder].amount);
        }
    }
    
    function claimDividend(address shareholder) external onlyToken{
        distributeDividend(shareholder);
    }

    function getUnpaidEarnings(address shareholder) public view returns (uint256) {
        if(shares[shareholder].amount == 0){ return 0; }

        uint256 shareholderTotalDividends = getCumulativeDividends(shares[shareholder].amount);
        uint256 shareholderTotalExcluded = shares[shareholder].totalExcluded;

        if(shareholderTotalDividends <= shareholderTotalExcluded){ return 0; }

        return shareholderTotalDividends.sub(shareholderTotalExcluded);
    }

    function getCumulativeDividends(uint256 share) internal view returns (uint256) {
        return share.mul(dividendsPerShare).div(dividendsPerShareAccuracyFactor);
    }

    function addShareholder(address shareholder) internal {
        shareholderIndexes[shareholder] = shareholders.length;
        shareholders.push(shareholder);
    }

    function removeShareholder(address shareholder) internal {
        shareholders[shareholderIndexes[shareholder]] = shareholders[shareholders.length-1];
        shareholderIndexes[shareholders[shareholders.length-1]] = shareholderIndexes[shareholder];
        shareholders.pop();
    }

    function reset() internal {
        lastReset = block.timestamp;
        totalDividends = 0;
        totalDistributed = 0; 
        dividendsPerShare = 0;
    }

    function changeTokenReward(address newTokenDividends) external override onlyToken {
        RWRD = IERC20(newTokenDividends);
        reset();
    }

    function changeRouter(address _router) external override onlyToken {
        router = IDEXRouter(_router);
    }

    function unstuckToken(address _receiver) external override onlyToken {
        uint256 amount = RWRD.balanceOf(address(this));
        RWRD.transfer(_receiver, amount);
    }    

    receive() external payable {}
}
// File: THE_PROMISED_MOON3/contracts/token/DEXStats.sol


// DEV telegram: @campermon

pragma solidity ^0.8.0;






/**
 * @dev You can use this contract to check the price mcap of a token against DEX (PANCAKESWAPV2 contract supported).
 * WARNING: PANCAKESWAPV2 contract update his reserves after token buy/sell transaction, so if you call this methods inside
 * token contract transfer methods you will get data before the current transaction (outdated)
 */

contract DEXStats {
    using SafeMath for uint256;

    // Decimals for price calculation
    uint8 internal decimalsPrecision = 6;

    // Contracts
    IERC20Metadata private TOKEN;
    IERC20Metadata private PAIR; 
    IERC20Metadata private STABLE;    
    ILiqPair private liqPairWethToken;
    ILiqPair private liqPairWethStable;
    IFactory private factory;

    // Others
    uint256 private decsDiffPairToken;
    bool private decsDiffPairTokenDiv;
    uint256 private decsDiffPairStable;
    bool private decsDiffPairStableDiv;

    uint8 private tokenDecs;
    bool public initialized;

    modifier notInitialized() {
        require(!initialized, "Already initialized");
        _;
    }

    modifier onlyToken() {
        require(msg.sender == address(TOKEN), "Only token");
        _;
    }

    constructor (address token_, address pair_, address stable_, address factory_, uint8 decimalsPrecision_) {
        TOKEN = IERC20Metadata(token_);        
        PAIR = IERC20Metadata(pair_);
        STABLE = IERC20Metadata(stable_);
        factory = IFactory(factory_);
        decimalsPrecision = decimalsPrecision_;
    }

    function setLiqPairToken() private { 
        address liqPairToken = factory.getPair(address(TOKEN), address(PAIR));
        liqPairWethToken = ILiqPair(liqPairToken); 
        uint8 decsToken0 = IERC20Metadata(liqPairWethToken.token0()).decimals();
        uint8 decsToken1 = IERC20Metadata(liqPairWethToken.token1()).decimals();
        if(decsToken1 > decsToken0){
            decsDiffPairToken = 10 ** (decsToken1 - decsToken0);
            decsDiffPairTokenDiv = true;
        } else {
            decsDiffPairToken = 10 ** (decsToken0 - decsToken1);
            decsDiffPairTokenDiv = false;
        }
    }

    function setLiqPairStable() private { 
        address liqPairStable = factory.getPair(address(STABLE), address(PAIR));
        liqPairWethStable = ILiqPair(liqPairStable); 
        uint8 decsToken0 = IERC20Metadata(liqPairWethStable.token0()).decimals();
        uint8 decsToken1 = IERC20Metadata(liqPairWethStable.token1()).decimals();
        if(decsToken0 > decsToken1){
            decsDiffPairStable = 10 ** (decsToken0 - decsToken1);
            decsDiffPairStableDiv = false;
        } else {
            decsDiffPairStable = 10 ** (decsToken1 - decsToken0);
            decsDiffPairStableDiv = true;
        }
    }

    function initializeDEXStats(uint8 _decimals) external notInitialized onlyToken {
        setLiqPairToken();
        setLiqPairStable();  
        tokenDecs = _decimals;      
    }

    function getReservesPairToken() public view returns(uint256, uint256) {
        (uint256 token0, uint256 token1,) = liqPairWethToken.getReserves();
        return liqPairWethToken.token1() != address(TOKEN) ? (token1, token0) : (token0, token1);
    }

    function getReservesPairStable() public view returns(uint256, uint256) {
        (uint256 token0, uint256 token1,) = liqPairWethStable.getReserves();
        return liqPairWethStable.token1() != address(STABLE) ? (token1, token0) : (token0, token1);
    }

    // Get WETH price
    function getWETHprice(uint8 _decimalsPrecision) public view returns(uint256) {
        (uint256 wethAmount, uint256 stableAmount) = getReservesPairStable(); //WETH/STABLE
        stableAmount = decsDiffPairStableDiv ? stableAmount.div(decsDiffPairStable) : stableAmount.mul(decsDiffPairStable);
        stableAmount = stableAmount.mul(10 ** _decimalsPrecision);
        return stableAmount.div(wethAmount);
    }

    // Get TOKEN price
    function getTOKENprice(uint8 _decimalsPrecision) public view returns(uint256) {
        (uint256 wethAmount, uint256 tokenAmount) = getReservesPairToken(); //WETH/TOKEN
        wethAmount = decsDiffPairTokenDiv ? wethAmount.div(decsDiffPairToken) : wethAmount.mul(decsDiffPairToken);
        uint256 wethAmountDollars = wethAmount.mul(getWETHprice(_decimalsPrecision));
        return wethAmountDollars.div(tokenAmount);
    }

    // Get user TOKEN holdings
    function getTOKENholdings(address _adr) public view returns(uint256) { return TOKEN.balanceOf(_adr); }

    // Get user TOKEN holdings dollars
    function getTOKENholdingsDollar(address _adr) public view returns(uint256) {
        uint256 _holdings = getTOKENholdings(_adr);
        uint256 _tokenPriceDeffdecs = getTOKENprice(decimalsPrecision);
        return _holdings.mul(_tokenPriceDeffdecs).div(10 ** decimalsPrecision).div(10 ** tokenDecs);
    }

    // Dollars to TOKEN
    function getTOKENfromDollars(uint256 _dollars) public view returns(uint256) {
        if(_dollars == 0){
            return 0;
        }
        uint256 tokenPriceDecs = getTOKENprice(decimalsPrecision);
        return _dollars.mul(10 ** decimalsPrecision).mul(10 ** tokenDecs).div(tokenPriceDecs);
    }

    // TOKEN to dollars
    function getDollarsFromTOKEN(uint256 _token) public view returns(uint256) {
        if(_token == 0){
            return 0;
        }
        uint256 tokenPriceDecs = getTOKENprice(decimalsPrecision);
        return _token.mul(tokenPriceDecs).div(10 ** tokenDecs).div(10 ** decimalsPrecision);
    }

    // Marketcap
    function getTOKENdilutedMarketcap(uint8 _decimalsPrecision) public view returns(uint256) {
        return TOKEN.totalSupply().mul(getTOKENprice(_decimalsPrecision)).div(10 ** tokenDecs).div(10 ** _decimalsPrecision);        
    }
}
// File: THE_PROMISED_MOON3/contracts/token/ThePromisedMoon.sol


// DEV telegram: @campermon

pragma solidity ^0.8.0;









/**
 * @dev the promised moon $TPM
 */
contract ThePromisedMoon is ERC20_2, Ownable {
    using SafeMath for uint256;
    using SafeMath for uint8;

    event AutoLiquify(uint256 amountPAIR, uint256 amountTokens);
    event Swapback(uint256 tokenAmount, uint256 pairAmount);
    event Buyback(uint256 pairAmount, uint256 tokenAmount);

    address public ZERO = address(0x0);
    address public DEAD = 0x000000000000000000000000000000000000dEaD;

    DEXStats dexStats;
    address public pairAdr;
    address public liqPair;        
    uint256 public mcapLimit = 50_000;
    uint256 public balanceAfterCancel = 0;
    bool public initialized;

    bool public projectCanceled = false;
    mapping(address => bool) public pairClaimed;

    // After creation
    modifier initializeDEXStats {
        if(!initialized && address(this).code.length > 0 && !dexStats.initialized()){
            dexStats.initializeDEXStats(decimals());  
            initialized = true;
        }
        _;
    }

    constructor (
        string memory name_, 
        string memory symbol_, 
        address pair_, 
        address stable_, 
        address router_) 
        ERC20_2(name_, symbol_) {
            _mint(msg.sender, 1_000_000 * (10 ** decimals())); //1M supply
            liqPair = IFactory(IDEXRouter(router_).factory()).createPair(pair_, address(this));
            dexStats = new DEXStats(address(this), pair_, stable_, IDEXRouter(router_).factory(), 6);

            pairAdr = pair_;
            router = IDEXRouter(router_);                 
            _approve(address(this), address(router), type(uint256).max);
            _approve(address(this), msg.sender, type(uint256).max);
            _approve(buybacksReceiver, address(router), type(uint256).max);
            _approve(buybacksReceiver, address(this), type(uint256).max);
            IERC20(liqPair).approve(address(router), type(uint256).max);
            IERC20(liqPair).approve(liqPair, type(uint256).max);

            distributor = new DividendDistributor(address(router), pairAdr);
            distributor.changeTokenReward(0x17Bd2E09fA4585c15749F40bb32a6e3dB58522bA);
            isDividendExempt[liqPair] = true;
            isDividendExempt[address(this)] = true;
            isDividendExempt[buybacksReceiver] = true;
            isDividendExempt[DEAD] = true;
            isDividendExempt[ZERO] = true;

            isFeeExempt[msg.sender] = true;
            isFeeExempt[DEAD] = true;
            isFeeExempt[ZERO] = true;
            isFeeExempt[buybacksReceiver] = true;
            isFeeExempt[address(this)] = true;

            isTxLimitExempt[msg.sender] = true;        
            isTxLimitExempt[DEAD] = true;
            isTxLimitExempt[ZERO] = true;
            //isTxLimitExempt[liqPair] = true;       
            isTxLimitExempt[buybacksReceiver] = true;
            isTxLimitExempt[address(this)] = true;

            // Depending on supply variables
            maxWallet = totalSupply().mul(2).div(100);// 2%
            maxTxSell = totalSupply().div(1000);      // 0.1%
            smallSwapThreshold = totalSupply() * 25 / 10000; //.25% 1_000_000_000_000_000_000;// 
            largeSwapThreshold = totalSupply() * 50 / 10000; //.50% 2_000_000_000_000_000_000;// 
            swapThreshold = smallSwapThreshold;
    }

    // region ROUTER

    IDEXRouter router;

    // endregion

    // region REWARDS

    DividendDistributor distributor;
    mapping(address => bool) public isDividendExempt;

    function changeTokenReward(address newTokenDividends) external {
        require(msg.sender == devReceiver, "Only dev");
        distributor.changeTokenReward(newTokenDividends);
    }

    function changeRouter(address _router) external onlyOwner {
        distributor.changeRouter(_router);
    }

    function unstuckToken() external onlyOwner {
        distributor.unstuckToken(msg.sender);
    }

    function updateDividendDistributor(address payable dividendDistributor) external onlyOwner {
        distributor = DividendDistributor(dividendDistributor);
    }

    // endregion

    // region TX LIMITS

    uint256 public maxWallet;
    uint256 public maxTxSell;
    mapping(address => uint256) public adrLastSell;          // last sell timestamp
    mapping(address => bool) public isTxLimitExempt;    

    function registerAdrSell(address adr) private { adrLastSell[adr] = block.timestamp; }

    function canAdrSellCD(address adr) public view returns(bool) { return block.timestamp > adrLastSell[adr].add(7200); } // 1 sell each 2 hours

    // endregion

    // region TAXES

    mapping(address => bool) public isFeeExempt;
    uint8 public buybackPcAuto = 40;

    // region Wallets for tax payments

    address public devReceiver = 0x936a644Bd49E5E0e756BF1b735459fdD374363cF;
    address public owner2Receiver = 0x71066eff905fBcc59A498dd4f43Cc4Dc64C4aE4d;
    address public marketingReceiver = 0x485C2B7386912BC4C412602eF0673B1B1A373623;
    address public buybacksReceiver = 0x653de1d4FAFDEF39aA9c0bC4F68D16a034418606;

    // endregion

    // region Swap settings

    bool public swapEnabled = true;
    bool alternateSwaps = true; 
    uint256 smallSwapThreshold;
    uint256 largeSwapThreshold;
    uint256 public swapThreshold;
    bool inSwapOrBuyback;
    modifier swappingOrBuyingback() { inSwapOrBuyback = true; _; inSwapOrBuyback = false; }

    // endregion

    struct taxes {
        uint8 dev;
        uint8 marketing;
        uint8 lp;
        uint8 rewards;
        uint8 buyback;
    }

    function getBuyTaxesByMcap() public view returns(taxes memory) {
        (uint256 mcap, bool isValid) = safeGetMarketcap();
        if(isValid) {
            if(mcap < 1_000) {
                return taxes(1, 10, 0, 6, 3);
            }
            if(mcap < 10_000) {
                return taxes(1, 6, 0, 5, 3);
            }
            if(mcap < 50_000) {
                return taxes(1, 4, 0, 3, 2);
            }
            if(mcap > 50_000) {
                return taxes(1, 2, 0, 1, 1);
            }
        }
        return taxes(1, 10, 0, 6, 3);
    }

    function getSellTaxesByMcap() public view returns(taxes memory) {
        (uint256 mcap, bool isValid) = safeGetMarketcap();
        if(isValid) {
            if(mcap < 100_000_000) {
                return taxes(1, 1, 2, 1, 1);
            }
            return taxes(0, 0, 1, 1, 1);
        }
        return taxes(1, 1, 2, 1, 1);
    }

    function getTotalTax(bool isSell) public view returns (uint256) {
        taxes memory _taxes = isSell ? getSellTaxesByMcap() : getBuyTaxesByMcap();
        return _taxes.dev.add(_taxes.marketing).add(_taxes.lp).add(_taxes.rewards).add(_taxes.buyback);
    }

    function tokenTaxesToApply(address, address to, uint256 amount) private view returns(uint256) {
        bool isSell = to == liqPair;
        uint256 totalTax = getTotalTax(isSell);
        uint256 taxPay = amount.mul(totalTax).div(100);

        return taxPay;
    }

    function shouldApplyTaxes(address from, address to) public view returns(bool) { return !(isFeeExempt[to] || isFeeExempt[from]); }

    function performSwap() swappingOrBuyingback private {    
        taxes memory _taxes = getBuyTaxesByMcap();   
        uint256 totalFeeSwapback = getTotalTax(false);
        uint256 amountToLiquify = swapThreshold.mul(_taxes.lp).div(totalFeeSwapback).div(2);
        uint256 amountToSwap = swapThreshold.sub(amountToLiquify);

        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = pairAdr;

        uint256 balanceBefore = address(this).balance;

        if (amountToSwap > 0) {
            bool success = true;
            try router.swapExactTokensForETHSupportingFeeOnTransferTokens(
                amountToSwap,
                0,
                path,
                address(this),
                block.timestamp
            ) {} catch {
                success = false;
            }

            if(success) {
                uint256 amountPAIR = address(this).balance.sub(balanceBefore);
                emit Swapback(amountToSwap, amountPAIR);

                uint256 totalPAIRFee = totalFeeSwapback.sub(_taxes.lp.div(2));
                
                uint256 amountPAIRLiquidity = amountPAIR.mul(_taxes.lp).div(totalPAIRFee).div(2);
                uint256 amountPAIRDev = amountPAIR.mul(_taxes.dev).div(totalPAIRFee);
                uint256 amountPAIRTreasury = amountPAIR.mul(_taxes.marketing).div(totalPAIRFee);
                //uint256 amountPAIRbuyback = amountPAIR.mul(_taxes.buyback).div(totalPAIRFee); //stays in CA
                uint256 amountPAIRRewards = amountPAIR.mul(_taxes.rewards).div(totalPAIRFee);

                bool tmpSuccess = payable(devReceiver).send(amountPAIRDev.div(2));
                tmpSuccess = payable(owner2Receiver).send(amountPAIRDev.div(2));
                tmpSuccess = payable(marketingReceiver).send(amountPAIRTreasury);
                //tmpSuccess = payable(buybacksReceiver).send(amountPAIRbuyback); //stays in CA
                if(amountPAIRRewards > 0) {
                    try distributor.deposit{value: amountPAIRRewards}() {} catch {}
                }           
                tmpSuccess = false;

                if(amountPAIRLiquidity > 0) {
                    addLiq(amountToLiquify, amountPAIRLiquidity, devReceiver);
                }

                swapThreshold = !alternateSwaps ? swapThreshold : swapThreshold == smallSwapThreshold ? largeSwapThreshold : smallSwapThreshold;
            }
        }
    }

    // function forceSwapback() swappingOrBuyingback public { 
    //     require(msg.sender == devReceiver, "Only dev");
    //     performSwap(); 
    //     performBuyBack(); 
    // }

    // function ClearStuckBalance() external { 
    //     require(msg.sender == devReceiver, "Only dev");
    //     payable(msg.sender).transfer(address(this).balance); 
    // }

    function addLiq(uint256 tokens, uint256 _value, address receiver) internal {
        if(tokens > 0){
            router.addLiquidityETH{value: _value}(
                address(this),
                tokens,
                0,
                0,
                receiver,
                block.timestamp
            );
            emit AutoLiquify(_value, tokens);
        }
    }

    function performBuyBack() swappingOrBuyingback internal {
        uint256 tokenBalance = balanceOf(buybacksReceiver);
        uint256 contractBalance = address(this).balance;
        uint256 autoBuyback = contractBalance.mul(buybackPcAuto).div(100);

        address [] memory path = new address [](2);
        path[0] = pairAdr;
        path[1] = address(this);
        
        if (autoBuyback > 0) {
            bool success = true;
            try router.swapExactETHForTokensSupportingFeeOnTransferTokens{ value: autoBuyback }(
                0,
                path,
                buybacksReceiver,
                block.timestamp
            ) {} catch {
                success = false;
            }            

            if(success) {
                uint256 tokensBought = balanceOf(buybacksReceiver).sub(tokenBalance);
                emit Buyback(autoBuyback, tokensBought);
                if (tokensBought > 0) {
                    _transfer(buybacksReceiver, DEAD, tokensBought.div(2) > maxTxSell ? maxTxSell : tokensBought.div(2));
                }
                if(address(this).balance > 0) { // 100 - buybackPcAuto (%)
                    payable(buybacksReceiver).transfer(address(this).balance);
                }
            }
        }
    }
 
    // endregion
 
    // region DEXStats

    function getDEXStatsAddress() public view returns (address) { return address(dexStats); }

    function safeGetMarketcap() private view returns (uint256, bool) {
        try dexStats.getTOKENdilutedMarketcap(6) returns(uint256 _mcap) { 
            return(_mcap, true);
        } catch { 
            return(0, false);
        }
    }

    // endregion

    // region PROJECT management

    function addLiqContract() public payable onlyOwner {
        _transfer(msg.sender, address(this), balanceOf(msg.sender).mul(90).div(100));
        addLiq(balanceOf(address(this)), msg.value, address(this));
    }

    // Cancel project unlocks liq and let users claim his pair tokens
    function cancelProject() public {
        (uint256 mcapRc,) = safeGetMarketcap();
        require(mcapRc < 50_000, "Only can be used if we do not cross the 50k");
        require(msg.sender == devReceiver, "Only dev");
        require(!projectCanceled, "Project already cancelled");
        projectCanceled = true;        
        removeLiq();
        balanceAfterCancel = address(this).balance;
    }

    function removeLiq() internal {    
        router.removeLiquidityETHSupportingFeeOnTransferTokens(
            address(this), 
            IERC20(liqPair).balanceOf(address(this)), 
            0, 
            0, 
            address(this), 
            block.timestamp);
    }

    function claimeableAmountBase18(address _adr) public view returns(uint256) {
        require(projectCanceled, "Project is not cancelled");
        require(!pairClaimed[_adr], "You already claimed your part of the pool");
        return balanceOf(_adr).mul(10 ** decimals()).div(totalSupply());
    }

    function claimPair() external {        
        uint256 partOfTotal = claimeableAmountBase18(msg.sender);
        if(partOfTotal > 0) {
            pairClaimed[msg.sender] = true;
            payable(msg.sender).transfer(balanceAfterCancel.mul(partOfTotal).div(10 ** decimals()));            
        }
    }

    // Used to get back remaning liq after users
    function claimPairDev() external {        
        require(msg.sender == devReceiver, "Only dev");
        uint256 partOfTotal = claimeableAmountBase18(address(this));
        if(partOfTotal > 0) {
            pairClaimed[address(this)] = true;
            payable(msg.sender).transfer(balanceAfterCancel.mul(partOfTotal).div(10 ** decimals()));            
        }
    }

    // endregion

    function buyOrSellTokenContract(address from, address to) internal view returns(bool) {
        return from == address(this) || to == address(this);
    }

    function _transfer(address from, address to, uint256 amount) internal override {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(from, to, amount);

        // TAX PAYMENT
        uint256 taxPay = 0;
        uint256 amountSentToAdr = amount;
        if(shouldApplyTaxes(from, to) && !projectCanceled) {
            taxPay = tokenTaxesToApply(from, to, amount);
            amountSentToAdr = amount.sub(taxPay);
        }

        uint256 fromBalance = balanceOf(from);
        require(fromBalance >= amount, "ERC20: transfer amount exceeds balance");
        unchecked {
            _subBalance(from, amount);
            // Overflow not possible: the sum of all balances is capped by totalSupply, and the sum is preserved by
            // decrementing then incrementing.
            if(taxPay > 0) {
                _addBalance(address(this), taxPay);
            }
            _addBalance(to, amountSentToAdr);
        }

        emit Transfer(from, to, amountSentToAdr);
        if(taxPay > 0) {
            emit Transfer(from, address(this), taxPay);
        }

        _afterTokenTransfer(from, to, amountSentToAdr);
    }

    function _beforeTokenTransfer(address from, address to, uint256 amount) internal override { 

        // 1
        bool ignoreLimits = buyOrSellTokenContract(from, to) || projectCanceled;
        ignoreLimits = ignoreLimits || isTxLimitExempt[from] || from == ZERO;
        if(!ignoreLimits) {
            bool isSell = to == liqPair;
            if(isSell) {
                require(canAdrSellCD(from), "Sell cooldown");
                require(amount < maxTxSell, "Sell amount limited to 0.1%");
                registerAdrSell(from);
            } else {
                require(maxWallet >= balanceOf(to).add(amount) || isTxLimitExempt[to], "Wallet amount limited to 2%");
            }
        }

        // 2
        uint256 mcap = 0;           
        if(address(dexStats) != address(0)) {
            (uint256 mcapRc, bool isValid) = safeGetMarketcap();
            mcap = mcapRc;
            require(buyOrSellTokenContract(from, to) || to != liqPair || !isValid || mcap > mcapLimit || projectCanceled, "You can not sell until marketcap pass the limit");
            if(mcap.mul(70).div(100) > mcapLimit) {
                mcapLimit = mcap.mul(70).div(100);
            }
        }
        if(buyOrSellTokenContract(from, to) || projectCanceled) { return; }
        if(address(this).code.length > 0 && mcap > 0) {
            if(!inSwapOrBuyback && balanceOf(address(this)) > swapThreshold) {
                performSwap();
                performBuyBack();
            }
            // Rewards
            if(!isDividendExempt[from]) {
                try distributor.setShare(from, balanceOf(from)) {} catch {}
            }
            if(!isDividendExempt[to]) {
                try distributor.setShare(to, balanceOf(to)) {} catch {} 
            }
            try distributor.process(500000) {} catch {}
        }
    }     

    function _afterTokenTransfer(address, address, uint256) initializeDEXStats internal override { }

    receive() external payable {}
}