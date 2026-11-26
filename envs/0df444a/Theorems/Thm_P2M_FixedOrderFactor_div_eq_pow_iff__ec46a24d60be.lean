-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_div_eq_pow_iff__ec46a24d60be
-- name    : P2M_FixedOrderFactor_div_eq_pow_iff__ec46a24d60be
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:13.850701+00:00
-- url     : https://prove2.me/theorems/f35cef75-41c7-438c-81f3-120e3d53704c
-- title:
--   P2 M Fixed Order Factor div eq pow iff  ec46a24d60be: P2 M Fixed Order Factor div eq pow iff  ec46a24d60be
-- statement:
--   **The surviving pairs.** For positive integers `m, n`, the quotient `m/n` is the `r`-th power
--   of a rational number exactly when `m = d aʳ` and `n = d bʳ` with `a, b` coprime.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Pairs.lean#L13-L50
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Pairs.lean#L13-L50

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Pairs
set_option autoImplicit true
@[expose] public section
public section
open FixedOrderFactor

theorem P2M_FixedOrderFactor_div_eq_pow_iff__ec46a24d60be {r m n : ℕ} (hr : 0 < r) (hm : 0 < m) (hn : 0 < n) :
    (∃ q : ℚ, (m : ℚ) / n = q ^ r) ↔
      ∃ d a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ m = d * a ^ r ∧ n = d * b ^ r := by sorry

alias «FixedOrderFactor».«div_eq_pow_iff'» := P2M_FixedOrderFactor_div_eq_pow_iff__ec46a24d60be
