-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_correctionFactor_even__20a8b73c46be
-- name    : P2M_FixedOrderFactor_correctionFactor_even__20a8b73c46be
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:05.088021+00:00
-- url     : https://prove2.me/theorems/ebaeed4b-d2ee-4aef-8cd1-00b6ebcfbf1d
-- title:
--   P2 M Fixed Order Factor correction Factor even  20a8b73c46be: P2 M Fixed Order Factor correction Factor even  20a8b73c46be
-- statement:
--   The P2 M Fixed Order Factor correction Factor even  20a8b73c46be construction uses the P2 M Fixed Order Factor correction Factor even  20a8b73c46be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Values.lean#L43-L70
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Values.lean#L43-L70

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem P2M_FixedOrderFactor_correctionFactor_even__20a8b73c46be {k : ℕ} (hk : 0 < k) :
    correctionFactor ∅ (2 * k) =
      -((Nat.choose (4 * k) (2 * k) : ℝ) * (bernoulli (2 * k) : ℝ) ^ 2 /
        (2 * (bernoulli (4 * k) : ℝ))) := by sorry

alias «FixedOrderFactor».«correctionFactor_even'» := P2M_FixedOrderFactor_correctionFactor_even__20a8b73c46be
