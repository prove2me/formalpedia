-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_entropy_moments
-- name    : QuantumFunctionalEstimation.Master.Supplement.entropy_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:59:04.25721+00:00
-- url     : https://prove2.me/theorems/a9f478db-c43e-40c2-bb87-4d343f5049e9
-- title:
--   Lemma 5.2 — entropy moment matching
-- statement:
--   There are positive constants $c_0,c_{\log}$ witnessing Lemma 5.1, with $c_0\le1/4$, such that for every integer $K\ge2$ and $1\le M\le4K^2$, there are Borel laws $\nu_0,\nu_1$ supported on $[0,M]$, matching moments through $K+1$, with common mean $c_0M/K^2$ and
--   $$\mathbb E_{\nu_1}[-Y\log Y]-\mathbb E_{\nu_0}[-Y\log Y]\ge2c_{\log}c_0M/K^2.$$
--   This supplies the entropy moment separation used by Theorem 5.3.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
--   - encoding: the fixed approximation constants from Lemma 5.1 → existential constants satisfying LogWitness; reason: pins the uniform Lemma 5.1 inequality; shrinking its positive cutoff to at most 1/4 enlarges the approximation interval and preserves the lower bound
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 20 (PDF p. 22), Lemma 5.2

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Lemma 5.2, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem entropy_moments :
  ∃ c₀ cLog : ℝ, LogWitness c₀ cLog ∧
  ∀ K : ℕ, 2 ≤ K → ∀ M : ℝ, 1 ≤ M → M ≤ 4 * (K : ℝ)^2 →
  ∃ μ₀ μ₁ : ProbabilityMeasure ℝ,
    MatchingOn (K + 1) (Set.Icc 0 M) (c₀ * M / (K : ℝ)^2) μ₀ μ₁ ∧
    Integrable (fun x : ℝ => -x * Real.log x) (μ₀ : Measure ℝ) ∧
    Integrable (fun x : ℝ => -x * Real.log x) (μ₁ : Measure ℝ) ∧
    2 * cLog * c₀ * M / (K : ℝ)^2 ≤
      expectation (fun x => -x * Real.log x) μ₁ - expectation (fun x => -x * Real.log x) μ₀ := by sorry

end QuantumFunctionalEstimation.Master.Supplement
