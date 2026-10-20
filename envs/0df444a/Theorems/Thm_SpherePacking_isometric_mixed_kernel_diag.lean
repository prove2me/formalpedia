-- Prove2me | Theorems.Thm_SpherePacking_isometric_mixed_kernel_diag
-- name    : SpherePacking.isometric_mixed_kernel_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:37.266213+00:00
-- url     : https://prove2.me/theorems/ee32e32d-51a7-4c09-8f8d-fea6e6bd7b28
-- title:
--   SpherePacking.isometric_mixed_kernel_diag
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter
open scoped BigOperators InnerProductSpace

theorem SpherePacking.isometric_mixed_kernel_diag
    {α ι ρ F E : Type*} [Fintype ι] [Fintype ρ]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]
    (bE : OrthonormalBasis ι ℝ E)
    (bF : OrthonormalBasis ρ ℝ F)
    (f : α → F →ₗᵢ[ℝ] E) (x : α) :
    mixedHilbertSchmidtKernel bE
      (fun z => (f z).toLinearMap)
      (fun z => (f z).toLinearMap) x x =
      (Module.finrank ℝ F : ℝ) := by sorry
