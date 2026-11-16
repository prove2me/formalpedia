-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_power_moments
-- name    : QuantumFunctionalEstimation.Master.Supplement.power_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:01:24.38879+00:00
-- url     : https://prove2.me/theorems/d96c5d23-0382-4a59-aee7-eb867a028c1a
-- title:
--   Lemma 5.5 — power-trace moment matching
-- statement:
--   Fix any positive noninteger $\alpha$. There are positive $c_\alpha,\gamma_\alpha$ witnessing Lemma 5.4, with $\gamma_\alpha\le1/8$, such that every integer $K\ge2$ and every $1\le M\le K^2$ admit laws $\nu_0,\nu_1$ on $[0,M]$ matching moments through $K+1$, with common mean $\gamma_\alpha M/K^2$ and
--   $$\mathbb E_{\nu_1}Y^\alpha-\mathbb E_{\nu_0}Y^\alpha\ge\Delta_\alpha(M/K^2)^\alpha,\qquad\Delta_\alpha=2c_\alpha\gamma_\alpha^\alpha.$$
--   This is the power-trace moment input for the Rényi applications.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
--   - encoding: the fixed approximation constants from Lemma 5.4 → alpha-only existential constants satisfying PowerWitness; reason: pins the uniform Lemma 5.4 inequality and its positive cutoff at most 1/8
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 23 (PDF p. 25), Lemma 5.5

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Lemma 5.5, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem power_moments :
  ∀ α : ℝ, 0 < α → Noninteger α →
  ∃ c γ : ℝ, PowerWitness α c γ ∧
  ∀ K : ℕ, 2 ≤ K → ∀ M : ℝ, 1 ≤ M → M ≤ (K : ℝ)^2 →
  ∃ μ₀ μ₁ : ProbabilityMeasure ℝ,
    MatchingOn (K + 1) (Set.Icc 0 M) (γ * M / (K : ℝ)^2) μ₀ μ₁ ∧
    Integrable (fun x : ℝ => x ^ α) (μ₀ : Measure ℝ) ∧
    Integrable (fun x : ℝ => x ^ α) (μ₁ : Measure ℝ) ∧
    powerGap α c γ * (M / (K : ℝ)^2)^α ≤
      expectation (fun x => x ^ α) μ₁ - expectation (fun x => x ^ α) μ₀ := by sorry

end QuantumFunctionalEstimation.Master.Supplement
