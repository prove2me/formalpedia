-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_TranscendenceBounds_trdeg_intermediateField_adjoin_le_card
-- name    : PermanentFormulaLowerBound.TranscendenceBounds.trdeg_intermediateField_adjoin_le_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/58d10f47-ee74-45cc-9277-76a381be78a9
-- title:
--   PermanentFormulaLowerBound.TranscendenceBounds.trdeg_intermediateField_adjoin_le_card
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

theorem PermanentFormulaLowerBound.TranscendenceBounds.trdeg_intermediateField_adjoin_le_card
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (s : Finset E) :
    Algebra.trdeg F (IntermediateField.adjoin F (s : Set E)) ≤
      (s.card : Cardinal) := by sorry
