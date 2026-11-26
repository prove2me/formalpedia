-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_correctionFactor_eq_mul__b1856a05bcec
-- name    : P2M_FixedOrderFactor_correctionFactor_eq_mul__b1856a05bcec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:48:49.979223+00:00
-- url     : https://prove2.me/theorems/4fd2278f-b2d7-59a7-bc01-140417943ac0
-- title:
--   P2 M Fixed Order Factor correction Factor eq mul  b1856a05bcec: P2 M Fixed Order Factor correction Factor eq mul  b1856a05bcec
-- statement:
--   The P2 M Fixed Order Factor correction Factor eq mul  b1856a05bcec construction uses the P2 M Fixed Order Factor correction Factor eq mul  b1856a05bcec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L84-L105
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L84-L105

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem P2M_FixedOrderFactor_correctionFactor_eq_mul__b1856a05bcec (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    correctionFactor N r =
      correctionFactor ∅ r * ∏ q ∈ N, (1 - (1 / (q : ℝ)) ^ r) / (1 + (1 / (q : ℝ)) ^ r) := by sorry

alias «FixedOrderFactor».«correctionFactor_eq_mul'» := P2M_FixedOrderFactor_correctionFactor_eq_mul__b1856a05bcec
