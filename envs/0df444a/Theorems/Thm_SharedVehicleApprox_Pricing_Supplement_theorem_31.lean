-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_theorem_31
-- name    : SharedVehicleApprox.Pricing.Supplement.theorem_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:39:55.074891+00:00
-- url     : https://prove2.me/theorems/0645f01a-45f9-42bb-91b2-430ac700e8e0
-- title:
--   Theorem 31, p. 39 — approximation guarantee for redirection without prices (corrected: strongly connected routing; sign condition)
-- statement:
--   Consider the $m$-unit system with arrival rates $\varphi_{ij}\ge0$, constant per-ride rewards $I_{ij}$ and redirection costs $c_{ij}$. There is no pricing: every customer is served when a unit is present at the origin, and the only control is redirection of the units that end a trip. Let $(\tilde q,\tilde z)$ be an optimum of Algorithm 8 and $\tilde r_{ij}=\tilde z_{ij}/\sum_k\varphi_{ki}\tilde q_k$. Assume that the routing induced by $\tilde r$ is strongly connected or $\tilde q=0$, and that $\tilde q\ne0$ or every origin has $\sum_j\varphi_{ij}I_{ij}\ge0$. Let $\tilde\pi$ be a stationary law under $\tilde r$. Then, for every state-dependent redirection policy $r$ and every stationary law $\pi$ of it,
--
--   $$\mathrm{Obj}_m(\tilde r)\ \ge\ \frac{m}{m+n-1}\,\mathrm{Obj}_m(r).$$
--
--   The policy does not balance demand, so the guarantee rests on the comparison with the infinite-unit system.
--
--   **Formalization Note** The printed title says "demand redirection". The algorithm, its constraints and the proof ("Lemma 30 in place of Lemma 21 in the proof of Theorem 22") are supply redirection. The printed opening "onsider an for" is read "Consider any objective for".
--
--   Differences from the source:
--   - correction: no connectivity hypothesis → the routing φ̄ of r̃ (all quantiles 1) is strongly connected, or q̃ = 0; reason: false without it: n = 2, m = 2, φ_12 = φ_21 = 1, I = 1, c = 0, z̃_12 = z̃_21 = 1 sends every unit back to its origin; all units at node 1 earn 1 and one unit at each node earns 2, while 2/3 · 2 > 1. Excluded: q̃ ≠ 0 with reducible routing of r̃
--   - correction: any constant per-ride rewards → q̃ ≠ 0, or Σ_j φ_ij I_ij ≥ 0 at every origin; reason: false without it: n = 2, m = 1, φ_12 = φ_21 = 1, φ_ii = 0, I = −1, c = 0; q̃ = 0, r̃ = 0 earns −1, the same policy is a competitor, and −1 < 1/2 · (−1). Without prices no policy can refuse service, whereas the relaxation can choose q = 0. Excluded: instances with q̃ = 0 and a negative total reward rate Σ_j φ_ij I_ij at some origin. The repair only requires nonnegative total reward rate at each origin, not nonnegative individual ride rewards; when q̃ = 0 feasibility forces z̃ = 0 and the implemented policy has no redirection costs.
--   - reading: title "demand redirection without pricing"; first words "onsider an for" → supply redirection by Algorithm 8, for any constant per-ride rewards; reason: App. D.1, Algorithm 8 and the sentence before the theorem define supply redirection
--   - reading: Algorithm 8 lists no sign constraint on z → z_ij ≥ 0; reason: z are rates (§5.1), and a negative z would give negative probabilities
--   - reading: a cost c_ij, with no sign stated → any real c_ij; reason: the reading covers every cost matrix, so it is not a weaker one
--   - generalization: a policy r(X) redirects a unit whose trip ends at i to another node j → competitors use r_kij(x), which may depend on the origin k and the state before the trip, and may have j = i; reason: this includes every rule r_ij(x) and every rule of the state at arrival, so the bound specializes to the paper’s Opt_m
--   - encoding: Opt_m, the objective of the optimal state-dependent policy → every admissible state-dependent policy and every stationary law of it; reason: a bound against every (policy, law) pair is a bound against their supremum, with no attainment needed; p. 7 measures upper bounds against the best possible steady-state distribution
--   - encoding: the steady-state distribution, treated as unique (p. 7) → any probability vector on the finite state space that satisfies the balance equations; reason: the balance equations are the paper’s characterization of stationarity, and quantifying over all laws avoids assuming uniqueness
--   - encoding: the output of Algorithm 8 → any optimal solution of its relaxation; reason: the algorithm returns an optimum; the statement holds for each one and does not need existence
--   - generalization: the positive population and node counts of the vehicle-system setting → natural-number counts, including zero where the other hypotheses are satisfiable; reason: every positive source instance is retained. At m = 0 the only state is the zero-count state and objectives and flows are zero; at n = 0 and m > 0 no normalized stationary law exists. The availability maximum is used only with an explicit nonempty node type
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 39 (PDF 40), Theorem 31, continued on p. 40 (PDF 41); Algorithm 8, p. 39 (PDF 40)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm3
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_NoPricing

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Theorem 31, p. 39 (corrected: the routing of `r̃` is strongly connected unless `q̃ = 0`, and
`q̃ ≠ 0` unless the total reward rate at each origin is nonnegative): without prices, the redirection probabilities returned
by Algorithm 8 earn at least `m/(m+n−1)` times the objective of every state-dependent redirection
policy under every stationary law of it. The title says demand redirection; the algorithm and the
proof are supply redirection. -/
theorem theorem_31 {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (I c : Fin n → Fin n → ℝ) (qt : Fin n → ℝ) (zt rt : Fin n → Fin n → ℝ)
    (hopt : IsAlg8Optimal φ I c qt zt) (hrt : rt = noPriceRedirectProb φ qt zt)
    (hconn : SupportConnected (inducedDemand φ (fun _ _ => 1) rt) (fun _ _ => 1) ∨ qt = 0)
    (hsign : qt ≠ 0 ∨ ∀ i, 0 ≤ ∑ j, φ i j * I i j)
    (πt : (Fin n → ℕ) → ℝ) (hπt : IsRedirectStationary n m φ serveAll (toRedirect rt) πt)
    (r : (Fin n → ℕ) → Fin n → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hr : IsRedirectPolicy n m serveAll r) (hπ : IsRedirectStationary n m φ serveAll r π) :
    (m : ℝ) / ((m : ℝ) + n - 1) * redirectObj n m φ (constReward I) c serveAll r π ≤
      redirectObj n m φ (constReward I) c serveAll (toRedirect rt) πt := by sorry

end SharedVehicleApprox.Pricing.Supplement
