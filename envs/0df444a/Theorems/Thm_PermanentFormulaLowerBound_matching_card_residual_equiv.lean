-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matching_card_residual_equiv
-- name    : PermanentFormulaLowerBound.matching_card_residual_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/3e091fc4-12ea-449e-990b-5589b3f12846
-- title:
--   PermanentFormulaLowerBound.matching_card_residual_equiv
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin

theorem PermanentFormulaLowerBound.matching_card_residual_equiv
    {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (rows : T ↪ B) (cols : T ↪ A)
    (hcard : Fintype.card A = Fintype.card B) :
    Fintype.card
      ({a : A // a ∉ Set.range cols} ≃
        {b : B // b ∉ Set.range rows}) =
      (Fintype.card A - Fintype.card T).factorial := by sorry
