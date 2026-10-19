-- Prove2me | Theorems.Thm_SpherePacking_finiteGramCertificate_auxiliary_sum_lower
-- name    : SpherePacking.finiteGramCertificate_auxiliary_sum_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:37.266213+00:00
-- url     : https://prove2.me/theorems/17fe9401-6fe9-4d58-b84c-e5106da23f59
-- title:
--   SpherePacking.finiteGramCertificate_auxiliary_sum_lower
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

theorem SpherePacking.finiteGramCertificate_auxiliary_sum_lower
    {n k L : ℕ} {s : ℝ}
    (certificate : FiniteGramCertificate n k L)
    (C : SphericalCode n s) :
    (Jacobi.topEigenvalue n k L - s) *
        (∑ x ∈ C.points, ∑ y ∈ C.points,
          isometricPackingKernel certificate.fibre x y) ≤
      ∑ x ∈ C.points, ∑ y ∈ C.points,
        auxiliaryFiniteGramKernel certificate s x y := by sorry
