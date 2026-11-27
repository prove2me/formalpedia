-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_theorem_22
-- name    : SharedVehicleApprox.Pricing.Supplement.theorem_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T18:36:45.442891+00:00
-- url     : https://prove2.me/theorems/8e307888-335b-49c7-81dd-3c9cdf574042
-- title:
--   Theorem 22, p. 26 — approximation guarantee for supply redirection (corrected: strongly connected routing, denominator of r̃)
-- statement:
--   Consider the $m$-unit system with instantaneous rides, arrival rates $\varphi_{ij}\ge0$, reward curves concave on $[0,1]$ and redirection costs $c_{ij}$. Let $(\tilde q,\tilde z)$ be an optimum of Algorithm 3 and $\tilde r_{ij}=\tilde z_{ij}/\sum_k\varphi_{ki}\tilde q_{ki}$. Assume that the induced demand $\bar\varphi$ of $(\tilde q,\tilde r)$ has strongly connected support or that $\tilde q=0$, and let $\tilde\pi$ be a stationary law under $(\tilde q,\tilde r)$. Then, for every state-dependent pricing and redirection policy $(q,r)$ and every stationary law $\pi$ of it,
--
--   $$\mathrm{Obj}_m(\tilde q,\tilde r)\ \ge\ \frac{m}{m+n-1}\,\mathrm{Obj}_m(q,r),$$
--
--   where the objective is the rewards of rides minus $c_{ij}$ for each unit redirected from $i$ to $j$. Thus empty-vehicle rebalancing can be added to pricing without loss in the guarantee of Theorem 15.
--
--   **Formalization Note** Page 25 prints the denominator of $\tilde r_{ij}$ as $\sum_k\varphi_{ki}$, a misprint with which the theorem fails; the proof of Lemma 21 uses the denominator above.
--
--   Differences from the source:
--   - correction: no connectivity hypothesis → the support graph of φ̄ is strongly connected or q̃ = 0; reason: false without it: n = 2, m = 2, φ_ij = 1 for all pairs, I_11 = I_22 = 1, I_12 = I_21 = 0, c = 0; q̃ = identity, r̃ = 0, all units at node 1 earn 1 and one unit at each node earns 2, while 2/3 · 2 > 1. Excluded: nonzero q̃ with reducible routing
--   - correction: Algorithm 3 prints r̃_ij = z̃_ij / Σ_k φ_ki → r̃_ij = z̃_ij / Σ_k φ_ki q̃_ki (0 when the denominator is 0); reason: misprint: the text before Algorithm 3 and the third equality of the proof of Lemma 21 use this denominator. With the printed one, n = 2, φ_12 = 2, φ_21 = 1, φ_ii = 0, c = 0, R_12(q) = q(3 − 2q), R_21(q) = q gives q̃_12 = 3/4, q̃_21 = 1, z̃_21 = 1/2, infinite-unit availabilities (8/9, 1), and for m = 30 an objective below 3, less than 30/31 times the 30/31 · 13/4 earned by the repaired policy
--   - reading: Algorithm 3 lists no sign constraint on z → z_ij ≥ 0; reason: z are rates (§5.1), and a negative z would give negative probabilities
--   - reading: a cost c_ij, with no sign stated → any real c_ij; reason: the reading covers every cost matrix, so it is not a weaker one
--   - generalization: a policy r(X) redirects a unit whose trip ends at i to another node j → competitors use r_kij(x), which may depend on the origin k and the state before the trip, and may have j = i; reason: this includes every rule r_ij(x) and every rule of the state at arrival, so the bound specializes to the paper’s Opt_m
--   - encoding: Opt_m, the objective of the optimal state-dependent policy → every admissible state-dependent policy and every stationary law of it; reason: a bound against every (policy, law) pair is a bound against their supremum, with no attainment needed; p. 7 measures upper bounds against the best possible steady-state distribution
--   - encoding: the steady-state distribution, treated as unique (p. 7) → any probability vector on the finite state space that satisfies the balance equations; reason: the balance equations are the paper’s characterization of stationarity, and quantifying over all laws avoids assuming uniqueness
--   - generalization: per-ride rewards of prices, with I_ij(q) := I_ij(F_ij^{-1}(1 − q)) (pp. 6–8) → arbitrary real functions I_ij of the quantile, with R_ij(q) = q · I_ij(q); no F_ij; reason: every reward induced by value distributions is such a function, so the statement specializes to the paper’s
--   - encoding: the output of Algorithm 3 → any optimal solution of its relaxation; reason: the algorithm returns an optimum; the statement holds for each one and does not need existence
--   - generalization: the positive population and node counts of the vehicle-system setting → natural-number counts, including zero where the other hypotheses are satisfiable; reason: every positive source instance is retained. At m = 0 the only state is the zero-count state and objectives and flows are zero; at n = 0 and m > 0 no normalized stationary law exists. The availability maximum is used only with an explicit nonempty node type
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 26 (PDF 27), Theorem 22; Algorithm 3, p. 25 (PDF 26)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm3

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Theorem 22, p. 26 (corrected: the routing of `(q̃, r̃)` is strongly connected, unless `q̃ = 0`,
and the denominator misprint in `r̃` is repaired): the state-independent prices and redirection
probabilities returned by Algorithm 3 earn at least `m/(m+n−1)` times the objective of every
state-dependent pricing and redirection policy under every stationary law of it. -/
theorem theorem_22 {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (c qt zt rt : Fin n → Fin n → ℝ) (hopt : IsAlg3Optimal φ I c qt zt)
    (hrt : rt = redirectProb φ qt zt)
    (hconn : SupportConnected (inducedDemand φ qt rt) (fun _ _ => 1) ∨ qt = 0)
    (πt : (Fin n → ℕ) → ℝ)
    (hπt : IsRedirectStationary n m φ (toPolicy qt) (toRedirect rt) πt)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ)
    (hqr : IsRedirectPolicy n m q r) (hπ : IsRedirectStationary n m φ q r π) :
    (m : ℝ) / ((m : ℝ) + n - 1) * redirectObj n m φ I c q r π ≤
      redirectObj n m φ I c (toPolicy qt) (toRedirect rt) πt := by sorry

end SharedVehicleApprox.Pricing.Supplement
