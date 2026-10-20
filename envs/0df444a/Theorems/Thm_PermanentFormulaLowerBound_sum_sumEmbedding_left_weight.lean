-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_sum_sumEmbedding_left_weight
-- name    : PermanentFormulaLowerBound.sum_sumEmbedding_left_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/b81d52d7-d62e-47b7-afa0-cc70790b634c
-- title:
--   PermanentFormulaLowerBound.sum_sumEmbedding_left_weight
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

theorem PermanentFormulaLowerBound.sum_sumEmbedding_left_weight
    {F α β γ : Type*} [CommSemiring F]
    [Fintype α] [Fintype β] [Fintype γ]
    (w : (α ↪ γ) → F) :
    (∑ rho : (α ⊕ β ↪ γ),
      w (Function.Embedding.inl.trans rho)) =
        ((Fintype.card γ - Fintype.card α).descFactorial
          (Fintype.card β) : F) *
          ∑ rho : (α ↪ γ), w rho := by sorry
