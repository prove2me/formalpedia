-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_Supplement_rank_moments
-- name    : QuantumFunctionalEstimation.Master.Supplement.rank_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:11:12.81926+00:00
-- url     : https://prove2.me/theorems/2b3cc7cf-76c9-49b4-b961-a83e8da4239b
-- title:
--   Lemma 5.20 — rank moment matching
-- statement:
--   For every integer $K\ge2$, put $M=100K^2$. There exist Borel laws $\mu_0,\mu_1$ supported on $\{0\}\cup[1,M]$, matching all moments through $K$, with common mean exactly one and
--   $$\Pr_{\mu_1}(Y>0)-\Pr_{\mu_0}(Y>0)\ge\tfrac14.$$
--   The same pair construction supports both the rank-testing and MPS-testing applications.
--
--   Differences from the source:
--   - encoding: probability laws, expectations, states and successful estimators or testers → Borel probability measures with integrable moments, finite complex matrices and operational POVM or interaction predicates; reason: these represent the same objects; no finite-support, rank, qubit, algorithm or outcome restriction is imposed
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed p. 33 (PDF p. 35), Lemma 5.20

import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Rates
import Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Approximation
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Lemma 5.20, Qisheng Wang, STOC 2027 submission #451 (October 2026).
Full source domains and all regimes; see the local metadata for exact pages and encodings. -/
theorem rank_moments :
  ∀ K : ℕ, 2 ≤ K → ∃ μ₀ μ₁ : ProbabilityMeasure ℝ,
  MatchingOn K ({0} ∪ Set.Icc 1 (100 * (K : ℝ)^2)) 1 μ₀ μ₁ ∧
    1 / 4 ≤ positiveMass μ₁ - positiveMass μ₀ := by sorry

end QuantumFunctionalEstimation.Master.Supplement
