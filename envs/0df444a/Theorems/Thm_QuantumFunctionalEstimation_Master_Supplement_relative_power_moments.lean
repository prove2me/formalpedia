-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_relative_power_moments
-- name    : QuantumFunctionalEstimation.Master.Supplement.relative_power_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:02:00.641207+00:00
-- url     : https://prove2.me/theorems/2b60c4d6-acb8-4721-ba8d-9433694a0fb1
-- title:
--   Lemma 5.8 — relative power-moment separation
-- statement:
--   Fix any noninteger $\alpha>1$, and write $s=\lceil\alpha\rceil$, $\beta=s-\alpha\in(0,1)$. There exist $C_\alpha,c_\alpha,\delta_\alpha>0$ such that every integer $K\ge\alpha$ admits laws $\nu_0,\nu_1$ supported on $[c_\alpha K^{-2s/\beta},C_\alpha K^{2s/\beta}]$, matching moments through $K$, with common mean $1/2$. Writing $A_b=\mathbb E_{\nu_b}Y^\alpha$, both inequalities hold:
--   $$\delta_\alpha(A_0+A_1)\le|A_1-A_0|\le\tfrac12(A_0+A_1).$$
--   The absolute value agrees with the canonical PDF; the laws can subsequently be interchanged to orient the gap. The constants are local to this lemma and are not the witnesses of Lemma 5.4. This provides the relative separation for the second Rényi regime.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 24 (PDF p. 26), Lemma 5.8

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Lemma 5.8, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem relative_power_moments :
  ∀ α : ℝ, 1 < α → Noninteger α →
  ∃ C c δ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ ∧
  ∀ K : ℕ, α ≤ (K : ℝ) →
  ∃ μ₀ μ₁ : ProbabilityMeasure ℝ,
    MatchingOn K (Set.Icc (c * (K : ℝ)^(-kappa α / 2))
      (C * (K : ℝ)^(kappa α / 2))) (1 / 2) μ₀ μ₁ ∧
    Integrable (fun x : ℝ => x ^ α) (μ₀ : Measure ℝ) ∧
    Integrable (fun x : ℝ => x ^ α) (μ₁ : Measure ℝ) ∧
    δ * (expectation (fun x => x ^ α) μ₀ + expectation (fun x => x ^ α) μ₁) ≤
      |expectation (fun x => x ^ α) μ₁ - expectation (fun x => x ^ α) μ₀| ∧
    |expectation (fun x => x ^ α) μ₁ - expectation (fun x => x ^ α) μ₀| ≤
      (expectation (fun x => x ^ α) μ₀ + expectation (fun x => x ^ α) μ₁) / 2 := by sorry

end QuantumFunctionalEstimation.Master.Supplement
