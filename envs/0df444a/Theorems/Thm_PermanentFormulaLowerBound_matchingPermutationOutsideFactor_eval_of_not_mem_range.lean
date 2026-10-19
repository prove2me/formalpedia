-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_eval_of_not_mem_range
-- name    : PermanentFormulaLowerBound.matchingPermutationOutsideFactor_eval_of_not_mem_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/5bac9aa6-0605-4d06-8390-7ea2420ec955
-- title:
--   PermanentFormulaLowerBound.matchingPermutationOutsideFactor_eval_of_not_mem_range
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

theorem PermanentFormulaLowerBound.matchingPermutationOutsideFactor_eval_of_not_mem_range
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n)
    (hij : σ i = j) (houtside : (i, j) ∉ Set.range d)
    (ξ : matchingOutside d → ℂ) :
    MvPolynomial.eval ξ (matchingPermutationOutsideFactor d σ i) =
      ξ ⟨(i, j), houtside⟩ := by sorry
