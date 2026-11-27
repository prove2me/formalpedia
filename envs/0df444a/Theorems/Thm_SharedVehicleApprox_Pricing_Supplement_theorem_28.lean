-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_theorem_28
-- name    : SharedVehicleApprox.Pricing.Supplement.theorem_28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T18:38:40.314986+00:00
-- url     : https://prove2.me/theorems/5f7f4129-1089-4402-8fdf-2f6a0e4e07ce
-- title:
--   Theorem 28, p. 37 — approximation guarantee for point pricing (corrected: strongly connected demand graph)
-- statement:
--   Consider the $m$-unit system with arrival rates $\varphi_{ij}\ge0$ whose graph $\{(i,j):i\ne j,\ \varphi_{ij}>0\}$ is strongly connected, and with reward curves concave on $[0,1]$. Let $\tilde q\in[0,1]^n$ be an optimum of Algorithm 6, $\max\sum_{i,j}\varphi_{ij}R_{ij}(q_i)$ subject to $\sum_k\varphi_{ki}q_k=q_i\sum_j\varphi_{ij}$, and let $\tilde\pi$ be a stationary law when $\tilde q_i$ is quoted to every customer at a non-empty node $i$. Then, for every state-dependent point-pricing policy $q_i(x)$ and every stationary law $\pi$ of it,
--
--   $$\mathrm{Obj}_m(\tilde q)\ \ge\ \frac{m}{m+n-1}\,\mathrm{Obj}_m(q).$$
--
--   The guarantee of Theorem 15 therefore also holds when prices may depend only on the origin. The benchmark consists of point policies only.
--
--   **Formalization Note** Under strong connectivity of $\varphi$, a balanced point vector is either zero or positive at every node, so the hypothesis covers every implemented routing that is strongly connected and the case $\tilde q=0$.
--
--   Differences from the source:
--   - correction: no connectivity hypothesis in the statement; App. A (p. 34) assumes the graph {(i, j) : φ_ij > 0} strongly connected → that App. A assumption on φ; reason: false without it: n = 2, m = 2, φ = identity, I = 1; q̃ = (1, 1), all units at node 1 earn 1 and one unit at each node earns 2, while 2/3 · 2 > 1. Excluded: demand graphs that are not strongly connected
--   - encoding: Opt_m, the objective of the optimal state-dependent policy → every admissible state-dependent policy and every stationary law of it; reason: a bound against every (policy, law) pair is a bound against their supremum, with no attainment needed; p. 7 measures upper bounds against the best possible steady-state distribution
--   - encoding: the steady-state distribution, treated as unique (p. 7) → any probability vector on the finite state space that satisfies the balance equations; reason: the balance equations are the paper’s characterization of stationarity, and quantifying over all laws avoids assuming uniqueness
--   - generalization: per-ride rewards of prices, with I_ij(q) := I_ij(F_ij^{-1}(1 − q)) (pp. 6–8) → arbitrary real functions I_ij of the quantile, with R_ij(q) = q · I_ij(q); no F_ij; reason: every reward induced by value distributions is such a function, so the statement specializes to the paper’s
--   - encoding: the output of Algorithm 6 → any optimal solution of its relaxation; reason: the algorithm returns an optimum; the statement holds for each one and does not need existence
--   - generalization: the positive population and node counts of the vehicle-system setting → natural-number counts, including zero where the other hypotheses are satisfiable; reason: every positive source instance is retained. At m = 0 the only state is the zero-count state and objectives and flows are zero; at n = 0 and m > 0 no normalized stationary law exists. The availability maximum is used only with an explicit nonempty node type
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 37 (PDF 38), Theorem 28; Algorithm 6, p. 36 (PDF 37)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_PointPricing

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Theorem 28, p. 37 (corrected: the graph `{(i, j) : φ_ij > 0}` is strongly connected, as App. A
assumes): the point quantiles returned by Algorithm 6 earn at least `m/(m+n−1)` times the objective
of every state-dependent point-pricing policy under every stationary law of it. -/
theorem theorem_28 {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (hconn : SupportConnected φ (fun _ _ => 1))
    (qt : Fin n → ℝ) (hopt : IsAlg6Optimal φ I qt)
    (πt : (Fin n → ℕ) → ℝ) (hπt : IsStationary n m φ (toPolicy (pointQuantile qt)) πt)
    (q : (Fin n → ℕ) → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m (pointPolicy q)) (hπ : IsStationary n m φ (pointPolicy q) π) :
    (m : ℝ) / ((m : ℝ) + n - 1) * obj n m φ I (pointPolicy q) π ≤
      obj n m φ I (toPolicy (pointQuantile qt)) πt := by sorry

end SharedVehicleApprox.Pricing.Supplement
