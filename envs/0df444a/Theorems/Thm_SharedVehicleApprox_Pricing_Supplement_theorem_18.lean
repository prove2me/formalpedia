-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_theorem_18
-- name    : SharedVehicleApprox.Pricing.Supplement.theorem_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:34:42.515987+00:00
-- url     : https://prove2.me/theorems/200c880c-cbda-4d18-bc8d-298aae7ae35f
-- title:
--   Theorem 18, p. 21 — approximation guarantee for pricing with travel times (corrected: strongly connected support)
-- statement:
--   Consider the $m$-unit system with $m\ge100$, arrival rates $\varphi_{ij}\ge0$, exponential travel times with means $\tau_{ij}>0$ and reward curves $R_{ij}(q)=qI_{ij}(q)$ that are concave on $[0,1]$. Let $\varepsilon_m=2\sqrt{\ln m/m}$. Let $q'$ maximize $\sum_{i,j}\varphi_{ij}R_{ij}(q_{ij})$ over balanced $q\in[0,1]^{n\times n}$ with $\sum_{i,j}\varphi_{ij}\tau_{ij}q_{ij}\le m$. Let $\tilde q$ be the output of Algorithm 2: $(1-\varepsilon_m)q'$ if $\sum_{i,j}\varphi_{ij}\tau_{ij}q'_{ij}\ge m(1-\varepsilon_m)$, and $q'$ otherwise. Assume that the support graph of $\tilde q$ is strongly connected or that $\tilde q=0$, and let $\tilde\pi$ be a stationary law under $\tilde q$. Then, for every state-dependent policy $q$ on the states $(x,y)$ and every stationary law $\pi$ of it,
--
--   $$\mathrm{Obj}_m(\tilde q)\ \ge\ (1-\varepsilon_m)\Bigl(\frac{\sqrt{m\ln m}}{\sqrt{m\ln m}+n-1}-\frac{3}{\sqrt{m\ln m}}\Bigr)\max\{\mathrm{Obj}_m(q),0\}.$$
--
--   As the policy $q\equiv0$ earns zero, $\mathrm{Opt}_m\ge0$ and this implies the paper's $\mathrm{Obj}_m(\tilde q)/\mathrm{Opt}_m\ge(1-\varepsilon_m)(\cdots)$ whenever $\mathrm{Opt}_m>0$. State-independent prices are thus asymptotically optimal for a fixed network size, for any demand rates and delays.
--
--   **Formalization Note** The maximum with $0$ is needed because the factor is negative when $n$ is large relative to $m$: multiplying it by the negative objective of a poor policy would give a false inequality. The constant $3/\sqrt{m\ln m}$ is the printed one; the last display of the paper's proof concludes only with $3/\sqrt m$.
--
--   Differences from the source:
--   - correction: no connectivity hypothesis (p. 7 treats the stationary law as unique) → the support graph of q̃ is strongly connected or q̃ = 0; reason: false without it: n = 3, m = 100, φ_ij = 1, τ_ij = 0.01, I_ij = 1 for i = j and 0 otherwise; q̃ = identity is optimal and is not scaled, all units at node 1 earn at most 1, and units split over the nodes earn almost 3, with factor above 0.442. Excluded: nonzero q̃ with reducible routing
--   - encoding: Obj_m(q̃)/Opt_m ≥ factor → factor · max(Obj_m(q, π), 0) ≤ Obj_m(q̃, π̃); reason: Opt_m ≥ 0 as q ≡ 0 is admissible; for a nonnegative factor this is the product form of the ratio and needs no division
--   - generalization: a ratio, meaningful for Opt_m > 0 → also Obj_m(q̃) ≥ 0 when the factor is negative and the bound 0 ≤ Obj_m(q̃) when Opt_m = 0; reason: obtained with q ≡ 0; the statement implies the printed ratio whenever it is defined
--   - encoding: Opt_m, the objective of the optimal state-dependent policy → every admissible state-dependent policy and every stationary law of it; reason: a bound against every (policy, law) pair is a bound against their supremum, with no attainment needed; p. 7 measures upper bounds against the best possible steady-state distribution
--   - encoding: the steady-state distribution, treated as unique (p. 7) → any probability vector on the finite state space that satisfies the balance equations; reason: the balance equations are the paper’s characterization of stationarity, and quantifying over all laws avoids assuming uniqueness
--   - generalization: per-ride rewards of prices, with I_ij(q) := I_ij(F_ij^{-1}(1 − q)) (pp. 6–8) → arbitrary real functions I_ij of the quantile, with R_ij(q) = q · I_ij(q); no F_ij; reason: every reward induced by value distributions is such a function, so the statement specializes to the paper’s
--   - encoding: the output of Algorithm 2 → any optimal solution of its relaxation; reason: the algorithm returns an optimum; the statement holds for each one and does not need existence
--   - encoding: travel times exponential for notational convenience (p. 11) → exponential transit with rate 1/τ_ij, τ_ij > 0; reason: the paper’s stated model; its remark on general laws is not part of the theorem
--   - generalization: the positive population and node counts of the vehicle-system setting → natural-number counts, including zero where the other hypotheses are satisfiable; reason: every positive source instance is retained. At m = 0 the only state is the zero-count state and objectives and flows are zero; at n = 0 and m > 0 no normalized stationary law exists. The availability maximum is used only with an explicit nonempty node type
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 21 (PDF 22), Theorem 18; Algorithm 2, p. 22 (PDF 23)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_StationaryLaw
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_TravelTimes
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_Algorithm2

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Theorem 18, p. 21 (corrected: the support graph of `q̃` is strongly connected, unless
`q̃ = 0`): with travel times and `m ≥ 100`, the output `q̃` of Algorithm 2 with
`ε_m = 2 √(ln m / m)` earns at least
`(1 − ε_m) (√(m ln m) / (√(m ln m) + n − 1) − 3 / √(m ln m))` times `Opt_m`. As the policy
`q ≡ 0` earns `0`, the bound is stated against `max (obj q π) 0`. -/
theorem theorem_18 {n m : ℕ} (hm : 100 ≤ m) (φ τ : Fin n → Fin n → ℝ)
    (hφ : ∀ i j, 0 ≤ φ i j) (hτ : ∀ i j, 0 < τ i j) (I : Fin n → Fin n → ℝ → ℝ)
    (hR : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j))
    (q' qt : Fin n → Fin n → ℝ) (hopt : IsAlg2Optimal φ τ I m q')
    (hout : qt = alg2Output φ τ m (epsilon m) q')
    (hconn : SupportConnected φ qt ∨ qt = 0)
    (πt : TTState n → ℝ) (hπt : IsTTStationary n m φ τ (toTTPolicy qt) πt)
    (q : TTState n → Fin n → Fin n → ℝ) (π : TTState n → ℝ)
    (hq : IsTTPolicy n m q) (hπ : IsTTStationary n m φ τ q π) :
    delayFactor n m * max (ttObj n m φ I q π) 0 ≤ ttObj n m φ I (toTTPolicy qt) πt := by sorry

end SharedVehicleApprox.Pricing.Supplement
