-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_lemma_16
-- name    : SharedVehicleApprox.Pricing.Supplement.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:32:17.290296+00:00
-- url     : https://prove2.me/theorems/955bc811-dc8b-459b-91fb-772145c1e342
-- title:
--   Lemma 16, p. 19 — given M available units, the node queues form an M-unit Gordon–Newell network (corrected: strongly connected support)
-- statement:
--   Consider the $m$-unit system with travel times: arrival rates $\varphi_{ij}\ge0$, exponential transit times with means $\tau_{ij}>0$, and state-independent quantiles $q_{ij}\in[0,1]$ whose support graph $\{(a,b):a\ne b,\ \varphi_{ab}q_{ab}>0\}$ is strongly connected. Let $\pi$ be a stationary law, let $M$ be the number of units not in transit, and let $M_0$ satisfy $\mathbb P[M=M_0]>0$. Then:
--
--   1. the law of $(X_i)_i$ given $M=M_0$ is a stationary law of the $M_0$-unit network with instantaneous rides, the same quantiles and the same arrival rates;
--   2. for every positive solution $r$ of $\sum_jr_j\varphi_{ji}q_{ji}=r_i\sum_k\varphi_{ik}q_{ik}$ it is the Gordon–Newell law (4),
--   $$\mathbb P[X=x\mid M=M_0]=\frac{\prod_ir_i^{x_i}}{\sum_{x'\in S_{n,M_0}}\prod_ir_i^{x'_i}}\qquad(x\in S_{n,M_0}).$$
--
--   The lemma reduces availability with travel times to availability in instantaneous networks of random size, and is used for Lemma 17.
--
--   **Formalization Note** The first clause is the literal reading of "identical to an $M$-unit Gordon–Newell network"; the second is the formula used in the paper's proof.
--
--   Differences from the source:
--   - correction: no connectivity hypothesis (p. 7 treats the stationary law as unique) → the support graph of q is strongly connected; reason: n = 2, m = 2, φ ≡ 1, q is the identity, τ ≡ 1; fix one vehicle in each closed station/self-link subsystem and use its stationary product law. Conditional on both units being available the node law is δ_(1,1), while r = (1,1) gives the uniform Gordon–Newell law. Every service rate is positive. Excluded: reducible routing
--   - encoding: the steady-state distribution, treated as unique (p. 7) → any probability vector on the finite state space that satisfies the balance equations; reason: the balance equations are the paper’s characterization of stationarity, and quantifying over all laws avoids assuming uniqueness
--   - encoding: the distribution of an M-unit Gordon–Newell network → both its balance equations and its product form (4), for any positive solution r of the traffic equations; reason: under connectivity these describe the same law, and every positive solution is a multiple of r(q)
--   - generalization: the positive population and node counts of the vehicle-system setting → natural-number counts, including zero where the other hypotheses are satisfiable; reason: every positive source instance is retained. At m = 0 the only state is the zero-count state and objectives and flows are zero; at n = 0 and m > 0 no normalized stationary law exists. The availability maximum is used only with an explicit nonempty node type
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 19 (PDF 20), Lemma 16

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_StationaryLaw
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_TravelTimes

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Lemma 16, p. 19 (corrected: the support graph of `q` is strongly connected): conditioned on the
number `M₀` of available units, the node queues of the system with travel times follow the
`M₀`-unit Gordon–Newell network with the same quantiles and arrival rates. The conditional law is
stationary for that network and equals its product-form law (4). -/
theorem lemma_16 {n m : ℕ} (φ τ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (hτ : ∀ i j, 0 < τ i j) (q : Fin n → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1)
    (hconn : SupportConnected φ q)
    (π : TTState n → ℝ) (hπ : IsTTStationary n m φ τ (toTTPolicy q) π)
    (M₀ : ℕ) (hM : 0 < availableProb m π M₀) :
    IsStationary n M₀ φ (toPolicy q) (condNodeLaw m π M₀) ∧
      ∀ r : Fin n → ℝ, (∀ i, 0 < r i) → IsTraffic φ q r →
        condNodeLaw m π M₀ = productForm (fun j y => r j ^ y) M₀ := by sorry

end SharedVehicleApprox.Pricing.Supplement
