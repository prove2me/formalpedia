-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_theorem_34
-- name    : SharedVehicleApprox.Pricing.Supplement.theorem_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:41:42.3256+00:00
-- url     : https://prove2.me/theorems/089c85ab-9a5f-43d5-a1c0-904d9fb127b9
-- title:
--   Theorem 34, p. 40 — redirection without prices with travel times (corrected: strongly connected routing, rate limit of Algorithm 9)
-- statement:
--   Consider the system with $m\ge100$ units, arrival rates $\varphi_{ij}\ge0$, exponential travel times with means $\tau_{ij}>0$ for occupied and for empty trips, constant rewards $I_{ij}$, redirection costs $c_{ij}$ and no pricing. Let $(\tilde q,\tilde z)$ be an optimum of Algorithm 9: the program of Algorithm 8 with $\sum_{i,j}\tau_{ij}(\varphi_{ij}q_i+z_{ij})\le m$. Let $\tilde r_{ij}=\tilde z_{ij}/\sum_k\varphi_{ki}\tilde q_k$, assume that the routing it induces is strongly connected or $\tilde q=0$, and let $\tilde\pi$ be a stationary law under $\tilde r$. Write $\varepsilon_m=2\sqrt{\ln m/m}$ and
--
--   $$K=(1-\varepsilon_m)\Bigl(\frac{\sqrt{m\ln m}}{\sqrt{m\ln m}+n-1}-\frac{3}{\sqrt{m\ln m}}\Bigr).$$
--
--   1. If $\mathrm{Opt}_m$ is the least upper bound of the objectives over all state-dependent redirection policies and their stationary laws, and $\mathrm{Opt}_m\ne0$, then
--   $$\frac{\mathrm{Obj}_m(\tilde r)}{\mathrm{Opt}_m}\ge K.$$
--   2. If $\tilde q\ne0$ or every origin has $\sum_j\varphi_{ij}I_{ij}\ge0$, then for every state-dependent redirection policy $r$ and every stationary law $\pi$ of it,
--   $$\mathrm{Obj}_m(\tilde r)\ge K\max\{\mathrm{Obj}_m(r),0\}.$$
--
--   The theorem extends the guarantee of Theorem 18 to rebalancing without prices, the setting of Braverman, Dai, Liu and Ying, with a finite-$m$ bound.
--
--   **Formalization Note** Clause 1 is the printed ratio on the whole domain. Clause 2 is its product form. The product form needs the sign condition: when every policy loses money the ratio holds but says nothing about approximation. Algorithm 9 prints its rate limit as $\sum_{i,j}\varphi_{ij}\tau_{ij}q_i+z_{ij}\le m$, a misprint for the constraint of §5.4 used here. The constant $3/\sqrt{m\ln m}$ is the printed one.
--
--   Differences from the source:
--   - correction: no connectivity hypothesis → the routing φ̄ of r̃ (all quantiles 1) is strongly connected, or q̃ = 0; reason: false without it: n = 3, m = 100, φ_{i,i+1} = 1 cyclically, τ = 0.01, I = 1, c = 0, z̃_{i+1,i} = 1 sends every unit back to its origin; all units at node 1 earn at most 1 and units split over the nodes earn almost 3, with K above 0.442. Excluded: q̃ ≠ 0 with reducible routing of r̃
--   - correction: Algorithm 9 prints Σ_ij φ_ij τ_ij q_i + z_ij ≤ m → Σ_ij τ_ij (φ_ij q_i + z_ij) ≤ m; reason: misprint: §5.4 (p. 30) states this constraint. With the printed one, n = 2, m = 10^6, φ_12 = 1, φ_21 = 1/2, τ_21 = 1.5 · 10^6, other τ = 10^-6, I = 1, c = 0 allows q̃ = (1, 1), z̃_21 = 1/2, whose policy earns at most 1, while redirecting with probability 1/4 earns above 1.15 and K > 0.99
--   - encoding: Opt_m and the ratio Obj_m(r̃)/Opt_m → clause 1: any least upper bound Opt of the attained objectives, with Opt ≠ 0; reason: the set is nonempty and bounded above, so this is its supremum with no default value; the ratio is undefined at 0
--   - generalization: the ratio bound only → also clause 2: K · max(Obj_m(r, π), 0) ≤ Obj_m(r̃, π̃) when q̃ ≠ 0 or Σ_j φ_ij I_ij ≥ 0 at every origin; reason: an additional conclusion, the approximation guarantee in product form; clause 1 alone covers the printed claim
--   - reading: the model of App. D.2 is given by reference to §2.4 and §5.1 → occupied and empty units travel in separate link queues with mean τ_ij, and only occupied units may be redirected on arrival; reason: §5.1 says redirected units are not redirected again, and the rate limit of §5.4 charges τ_ij to both flows
--   - reading: Algorithm 9 lists no sign constraint on z → z_ij ≥ 0; reason: z are rates (§5.1), and a negative z would give negative probabilities
--   - reading: a cost c_ij, with no sign stated → any real c_ij; reason: the reading covers every cost matrix, so it is not a weaker one
--   - generalization: a policy r(X) redirects a unit whose trip ends at i to another node j → competitors use r_kij(x), which may depend on the origin k and the state before the trip, and may have j = i; reason: this includes every rule r_ij(x) and every rule of the state at arrival, so the bound specializes to the paper’s Opt_m
--   - encoding: the steady-state distribution, treated as unique (p. 7) → any probability vector on the finite state space that satisfies the balance equations; reason: the balance equations are the paper’s characterization of stationarity, and quantifying over all laws avoids assuming uniqueness
--   - encoding: the output of Algorithm 9 → any optimal solution of its relaxation; reason: the algorithm returns an optimum; the statement holds for each one and does not need existence
--   - generalization: the positive population and node counts of the vehicle-system setting → natural-number counts, including zero where the other hypotheses are satisfiable; reason: every positive source instance is retained. At m = 0 the only state is the zero-count state and objectives and flows are zero; at n = 0 and m > 0 no normalized stationary law exists. The availability maximum is used only with an explicit nonempty node type
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 40 (PDF 41), Theorem 34; Algorithm 9, p. 41 (PDF 42); §5.4, p. 30 (PDF 31)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_StationaryLaw
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_SupplyRedirection
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm3
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_NoPricing
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_TravelTimes
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_RedirectionTravelTimes

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Theorem 34, p. 40 (corrected: the routing of `r̃` is strongly connected unless `q̃ = 0`; the
rate-limit misprint of Algorithm 9 is repaired): without prices, with travel times and `m ≥ 100`,
let `r̃` be the output of Algorithm 9. Then (1) the printed ratio bound holds for the least upper
bound `Opt_m` of the objectives of state-dependent policies whenever `Opt_m ≠ 0`; (2) if `q̃ ≠ 0`
or the total reward rate at each origin is nonnegative, the approximation guarantee holds in product form. -/
theorem theorem_34 {n m : ℕ} (hm : 100 ≤ m) (φ τ : Fin n → Fin n → ℝ)
    (hφ : ∀ i j, 0 ≤ φ i j) (hτ : ∀ i j, 0 < τ i j)
    (I c : Fin n → Fin n → ℝ) (qt : Fin n → ℝ) (zt rt : Fin n → Fin n → ℝ)
    (hopt : IsAlg9Optimal φ τ I c m qt zt) (hrt : rt = noPriceRedirectProb φ qt zt)
    (hconn : SupportConnected (inducedDemand φ (fun _ _ => 1) rt) (fun _ _ => 1) ∨ qt = 0)
    (πt : RTState n → ℝ) (hπt : IsRTStationary n m φ τ (toRTPolicy rt) πt) :
    (∀ Opt : ℝ,
      IsLUB {v : ℝ | ∃ r π, IsRTPolicy n m r ∧ IsRTStationary n m φ τ r π ∧
        v = rtObj n m φ τ I c r π} Opt →
      Opt ≠ 0 → delayFactor n m ≤ rtObj n m φ τ I c (toRTPolicy rt) πt / Opt) ∧
      ((qt ≠ 0 ∨ ∀ i, 0 ≤ ∑ j, φ i j * I i j) →
        ∀ (r : RTState n → Fin n → Fin n → Fin n → ℝ) (π : RTState n → ℝ),
          IsRTPolicy n m r → IsRTStationary n m φ τ r π →
            delayFactor n m * max (rtObj n m φ τ I c r π) 0 ≤
              rtObj n m φ τ I c (toRTPolicy rt) πt) := by sorry

end SharedVehicleApprox.Pricing.Supplement
