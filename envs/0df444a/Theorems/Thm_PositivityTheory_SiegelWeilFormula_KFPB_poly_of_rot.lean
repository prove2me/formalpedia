-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_poly_of_rot
-- name    : PositivityTheory.SiegelWeilFormula.KFPB.poly_of_rot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:10.496825+00:00
-- url     : https://prove2.me/theorems/f13f4a0e-1e8c-4d0a-a59b-436ac9e4deef
-- title:
--   KFPB: poly of rot
-- statement:
--   The KFPB construction uses the poly of rot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IteratedDerivScale.lean#L27-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/PolynomialGaussianIntegrals/IteratedDerivScale.lean#L27-L74

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Nat
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB

theorem PositivityTheory.SiegelWeilFormula.KFPB.poly_of_rot (q : Polynomial ℂ) (hq : q ≠ 0) (μ ω : ℂ) (hμ : μ ≠ 0) (hω0 : ω ≠ 0)
    (hω : ∀ j : ℕ, 0 < j → ω ^ j ≠ 1) :
    ∃ N : ℕ, ∀ E : ℂ → ℂ, Differentiable ℂ E →
      (∀ z, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * μ ^ i * E (ω ^ i * z) = 0) →
      ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ z, E z = p.eval z := by sorry
