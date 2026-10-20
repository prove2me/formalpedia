-- Prove2me | Theorems.Thm_SpherePacking_SpectralAsymptotics_tridiagonal_quadratic_sum
-- name    : SpherePacking.SpectralAsymptotics.tridiagonal_quadratic_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:37.266213+00:00
-- url     : https://prove2.me/theorems/54441965-9813-4ec7-ac39-2ef74f634a86
-- title:
--   SpherePacking.SpectralAsymptotics.tridiagonal_quadratic_sum
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
open Filter Topology
open scoped BigOperators Topology InnerProductSpace
open SpherePacking.SpectralAsymptotics
open SpherePacking.NumericalCertificate

theorem SpherePacking.SpectralAsymptotics.tridiagonal_quadratic_sum
    (d : ℕ) (c v : ℕ → ℝ) :
    (∑ p ∈ Finset.range (d + 1),
      ∑ q ∈ Finset.range (d + 1),
        (if p + 1 = q then c p
          else if q + 1 = p then c q else 0) * v q * v p) =
      2 * ∑ p ∈ Finset.range d, c p * v p * v (p + 1) := by sorry
