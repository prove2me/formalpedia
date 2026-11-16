-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_fidelity_moments
-- name    : QuantumFunctionalEstimation.Master.Supplement.fidelity_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:08:55.35742+00:00
-- url     : https://prove2.me/theorems/657df8f4-de40-4baa-ad0f-0333aca43cb2
-- title:
--   Lemma 5.17 — fidelity moment matching
-- statement:
--   For every integer $K\ge2$ and every $1\le M\le4K^2$, there are Borel laws $\nu_0,\nu_1$ supported on $[0,M]$, matching moments through $K+1$, with common mean $M/(32K^2)\le1/8$, and
--   $$\mathbb E_{\nu_1}\sqrt Y-\mathbb E_{\nu_0}\sqrt Y\ge\frac{\sqrt M}{48K}.$$
--   This is the moment input for unsquared Uhlmann fidelity estimation.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 32 (PDF p. 34), Lemma 5.17

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Lemma 5.17, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem fidelity_moments :
  ∀ K : ℕ, 2 ≤ K → ∀ M : ℝ, 1 ≤ M → M ≤ 4 * (K : ℝ)^2 →
  ∃ μ₀ μ₁ : ProbabilityMeasure ℝ,
    MatchingOn (K + 1) (Set.Icc 0 M) (M / (32 * (K : ℝ)^2)) μ₀ μ₁ ∧
    M / (32 * (K : ℝ)^2) ≤ 1 / 8 ∧
    Integrable Real.sqrt (μ₀ : Measure ℝ) ∧ Integrable Real.sqrt (μ₁ : Measure ℝ) ∧
    Real.sqrt M / (48 * K) ≤ expectation Real.sqrt μ₁ - expectation Real.sqrt μ₀ := by sorry

end QuantumFunctionalEstimation.Master.Supplement
