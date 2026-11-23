-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_theorem_23
-- name    : SharedVehicleApprox.Pricing.Supplement.theorem_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:37:38.730641+00:00
-- url     : https://prove2.me/theorems/529b4fd7-bf7b-43fd-b329-223f2ae05221
-- title:
--   Theorem 23, p. 27 — approximation guarantee for demand redirection (corrected: strongly connected routing)
-- statement:
--   Consider the $m$-unit system with instantaneous rides, arrival rates $\varphi_{ij}\ge0$, reward curves concave on $[0,1]$ and a graph $E$ of nearby nodes. A willing customer at $i$ is assigned to $i$ or to a node $k$ with $(i,k)\in E$, and is lost if that node is empty. Let $(\tilde q,\tilde z)$ be an optimum of Algorithm 4 and $\tilde r_{ik}=\tilde z_{ik}/\sum_j\varphi_{ij}\tilde q_{ij}$. Assume that the demand induced by $(\tilde q,\tilde r)$, $\bar\varphi_{kj}=\varphi_{kj}\tilde q_{kj}(1-\sum_l\tilde r_{kl})+\sum_i\varphi_{ij}\tilde q_{ij}\tilde r_{ik}$, has strongly connected support or that $\tilde q=0$, and let $\tilde\pi$ be a stationary law under $(\tilde q,\tilde r)$. Then, for every state-dependent pricing and matching policy $(q,r)$ and every stationary law $\pi$ of it,
--
--   $$\mathrm{Obj}_m(\tilde q,\tilde r)\ \ge\ \frac{m}{m+n-1}\,\mathrm{Obj}_m(q,r).$$
--
--   The theorem gives the guarantee of Theorem 15 when the platform also chooses from which nearby node each customer is served. The paper omits its proof as similar to that of Theorem 22.
--
--   Differences from the source:
--   - correction: no connectivity hypothesis → the support graph of φ̄ is strongly connected or q̃ = 0; reason: false without it: n = 2, m = 2, φ_ij = 1 for all pairs, I_11 = I_22 = 1, I_12 = I_21 = 0, E = ∅; all units at node 1 earn 1 and one unit at each node earns 2, while 2/3 · 2 > 1. Excluded: nonzero q̃ with reducible routing
--   - reading: Algorithm 4 lists no sign constraint on z → z_ij ≥ 0; reason: z are rates (§5.1), and a negative z would give negative probabilities
--   - reading: unavailability under matching is not spelled out → a quantile may be positive at an empty origin, and a customer assigned to an empty node is lost; reason: §5.1 serves customers from adjacent nodes, so forcing q_ij(x) = 0 at x_i = 0 would shrink Opt_m; this is the stronger reading
--   - generalization: a policy r(X) decides the serving node of a customer arriving at i → competitors use r_ijk(x), which may also depend on the destination j; reason: this includes every rule r_ik(x), so the bound specializes to the paper’s Opt_m
--   - encoding: Opt_m, the objective of the optimal state-dependent policy → every admissible state-dependent policy and every stationary law of it; reason: a bound against every (policy, law) pair is a bound against their supremum, with no attainment needed; p. 7 measures upper bounds against the best possible steady-state distribution
--   - encoding: the steady-state distribution, treated as unique (p. 7) → any probability vector on the finite state space that satisfies the balance equations; reason: the balance equations are the paper’s characterization of stationarity, and quantifying over all laws avoids assuming uniqueness
--   - generalization: per-ride rewards of prices, with I_ij(q) := I_ij(F_ij^{-1}(1 − q)) (pp. 6–8) → arbitrary real functions I_ij of the quantile, with R_ij(q) = q · I_ij(q); no F_ij; reason: every reward induced by value distributions is such a function, so the statement specializes to the paper’s
--   - encoding: the output of Algorithm 4 → any optimal solution of its relaxation; reason: the algorithm returns an optimum; the statement holds for each one and does not need existence
--   - generalization: the positive population and node counts of the vehicle-system setting → natural-number counts, including zero where the other hypotheses are satisfiable; reason: every positive source instance is retained. At m = 0 the only state is the zero-count state and objectives and flows are zero; at n = 0 and m > 0 no normalized stationary law exists. The availability maximum is used only with an explicit nonempty node type
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 27 (PDF 28), Theorem 23, continued on p. 28 (PDF 29) with Algorithm 4

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_DemandRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm4

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Theorem 23, p. 27 (corrected: the routing of `(q̃, r̃)` is strongly connected, unless
`q̃ = 0`): the state-independent prices and matching probabilities returned by Algorithm 4 earn at
least `m/(m+n−1)` times the objective of every state-dependent pricing and matching policy under
every stationary law of it. -/
theorem theorem_23 {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (E : Finset (Fin n × Fin n))
    (qt zt rt : Fin n → Fin n → ℝ) (hopt : IsAlg4Optimal φ I E qt zt)
    (hrt : rt = matchProb φ qt zt)
    (hconn : SupportConnected (matchDemand φ qt rt) (fun _ _ => 1) ∨ qt = 0)
    (πt : (Fin n → ℕ) → ℝ) (hπt : IsMatchStationary n m φ (toQuote qt) (toMatch rt) πt)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ)
    (π : (Fin n → ℕ) → ℝ)
    (hqr : IsMatchPolicy n m E q r) (hπ : IsMatchStationary n m φ q r π) :
    (m : ℝ) / ((m : ℝ) + n - 1) * matchObj n m φ I q r π ≤
      matchObj n m φ I (toQuote qt) (toMatch rt) πt := by sorry

end SharedVehicleApprox.Pricing.Supplement
