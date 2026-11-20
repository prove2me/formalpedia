-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_hub_stability_threshold
-- name    : StableMSR.Recovery.Supplement.hub_stability_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T03:16:18.705201+00:00
-- url     : https://prove2.me/theorems/90fe21d8-8919-47ad-b167-e09cb93b8c7d
-- title:
--   Proposition C.2 — exact stability threshold and metric tie
-- statement:
--   Use the rational hub/dummy construction of Appendix C with $1\le k\le |Y|$, $\tau>0$, and $\gamma>1$. Put $a=\mathrm{OPT}_k(Y)$ and
--
--   $$\lambda_*=(\delta+a)/R_0=\gamma+(\mathrm{OPT}_k(Y)-\tau)/R_0.$$
--
--   For every real $\lambda\ge1$, under each perturbation convention,
--
--   $$\mathcal O_0\text{ is }\lambda\text{-stable}\iff\lambda<\lambda_*.$$
--
--   There is also a metric $\lambda_*$-perturbation for which $\mathcal O_0$ is optimal and a distinct feasible exact-$K$ partition has equal cost. Perturbed distances may be real and centers may change. This records both directions of the exact threshold and the boundary tie.
--
--   Differences from the source:
--   - encoding: Finite ordered metric input and unordered exact-k partitions → Fin n points, real metric arrays, and finite sets of nonempty disjoint blocks; reason: Input-order relabelling preserves every source instance and partition; base published definitions are reused without extra conditions
--   - encoding: O_0 is lambda-stable exactly when 1 <= lambda < lambda*, and a metric tie at lambda* → The equivalences quantify over every real lambda >= 1, followed by an explicit metric perturbation and distinct equal-cost feasible competitor; reason: Lambda >= 1 is the domain of stability factors; the boundary witness is part of the conclusion, not an assumption
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Proposition C.2, p. 25; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Supplement_Hub

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

theorem hub_stability_threshold {n k : ℕ} (d : Point n → Point n → ℚ) (γ τ : ℚ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (hd : IsMetricArray (fun x y => (d x y : ℝ)))
    (hγ : 1 < γ) (hτ : 0 < τ) :
    let dr := fun x y => (d x y : ℝ)
    let dp := hubDistance dr k γ τ
    let O₀ := suppliedPartition n k
    let ellStar := stabilityThreshold dr k γ τ
    ellStar = (γ : ℝ) + (optimumValue dr k - τ) / hubRadius dr γ τ ∧
    (∀ ell : ℝ, 1 ≤ ell →
      (Stable dp (k + 2) ell O₀ ↔ ell < ellStar) ∧ (StableMetric dp (k + 2) ell O₀ ↔ ell < ellStar)) ∧
    ∃ p : Point (n + k + 2) → Point (n + k + 2) → ℝ,
      MetricPerturbation dp ellStar p ∧ Optimal p Finset.univ (k + 2) O₀ ∧
      ∃ Q, Feasible Finset.univ (k + 2) Q ∧ Q ≠ O₀ ∧ cost p Q = cost p O₀ := by sorry

end StableMSR.Recovery.Supplement
