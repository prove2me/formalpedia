-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_weighted_objective_sdp
-- name    : QAlgorithms.Papers.Independent.Information100.P19.weighted_objective_sdp
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:07:31.50578+00:00
-- url     : https://prove2.me/theorems/7b6a7e01-6467-48ef-8ea5-66425518d11c
-- title:
--   Proposition A.1
-- statement:
--   Fix $k\ge1$ and $0\le\beta<3/2$. For $h(x)=\sum_{j=1}^ka_jx^j$ with $h(1)=1$, feasibility $h\le\sqrt x$ on $[0,1]$ is equivalent to
--   $$t-h(t^2)=Q(t)+t(1-t)S(t),$$
--   where $Q,S$ are sums of squares with degree bounds $2k,2k-2$. The weighted integral is integrable and equals
--   $$E_\beta(h)=\frac2{3-2\beta}-\sum_{j=1}^k\frac{a_j}{j+1-\beta}.$$
--   Consequently minimization is equivalent to maximizing the displayed linear sum under the SOS certificate. The objective is affine, preserving the constant term that the source calls linear.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 51, Proposition A.1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition A.1; arXiv:2609.29471v1, PDF pp.51, 52. -/
theorem weighted_objective_sdp (k : ℕ) (hk : 1≤k) (beta : ℝ) (hbeta : 0≤beta) (hbeta1 : beta<3/2) :
    (∀ h : Polynomial ℝ, minorantFeasible k h ↔ sosFeasible k h) ∧
    (∀ h : Polynomial ℝ, sosFeasible k h →
      IntegrableOn (fun x : ℝ => Real.rpow x (-beta)*(Real.sqrt x-h.eval x)) (Set.Ioc 0 1) ∧
      weightedError beta hbeta hbeta1 h = 2/(3-2*beta)-weightedScore k beta h) ∧
    (∀ h : Polynomial ℝ, WeightedOptimizer k beta h ↔
      sosFeasible k h ∧ ∀ g : Polynomial ℝ, sosFeasible k g →
        weightedScore k beta g ≤ weightedScore k beta h) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
