-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_TranscendenceBounds_trdeg_intermediateField_le_of_adjoin_card_le
-- name    : PermanentFormulaLowerBound.TranscendenceBounds.trdeg_intermediateField_le_of_adjoin_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/4b103248-1bdb-441f-b5ce-14c653fcee35
-- title:
--   PermanentFormulaLowerBound.TranscendenceBounds.trdeg_intermediateField_le_of_adjoin_card_le
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
open PermanentFormulaLowerBound.TranscendenceBounds

theorem PermanentFormulaLowerBound.TranscendenceBounds.trdeg_intermediateField_le_of_adjoin_card_le
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K : IntermediateField F E) (s : Finset E) {budget : ℕ}
    (hK : K ≤ IntermediateField.adjoin F (s : Set E))
    (hbudget : s.card ≤ budget) :
    Algebra.trdeg F K ≤ (budget : Cardinal) := by sorry
