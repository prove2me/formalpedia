-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_Supplement_lemma_17
-- name    : SharedVehicleApprox.Pricing.Supplement.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:33:20.361065+00:00
-- url     : https://prove2.me/theorems/a19f9890-cf9f-41fe-8ba5-6523a53ef180
-- title:
--   Lemma 17, p. 20 — maximum availability with travel times (corrected: strongly connected support)
-- statement:
--   Consider the $m$-unit system with $n\ge1$ nodes, arrival rates $\varphi_{ij}\ge0$ and exponential travel times with means $\tau_{ij}>0$. Let $m\ge100$, and let $q\in[0,1]^{n\times n}$ have strongly connected support graph $\{(a,b):a\ne b,\ \varphi_{ab}q_{ab}>0\}$ and satisfy $\sum_{i,j}\varphi_{ij}\tau_{ij}q_{ij}\le m-2\sqrt{m\ln m}$. Then, under any stationary law, the maximum availability $A_m(q)=\max_i\mathbb P[X_i>0]$ satisfies
--
--   $$A_m(q)\ge\Bigl(1-\frac3{\sqrt m}\Bigr)\frac{\sqrt{m\ln m}}{\sqrt{m\ln m}+n-1}.$$
--
--   The demand need not be balanced. The bound tends to one as $m$ grows, including when demand grows in proportion to the supply, and it is the availability bound behind Theorem 18.
--
--   **Formalization Note** The logarithm is natural and the maximum is over the nonempty node set.
--
--   Differences from the source:
--   - correction: "For any network", with the stationary law treated as unique → the support graph of q is strongly connected; reason: n = 2, m = 100, φ ≡ 1, q is the identity, τ ≡ 0.01; mix the two stationary laws having all vehicles in one station/self-link subsystem with equal weights. Each availability is at most 1/2, the load is 0.02, and the printed lower bound is above 0.66. Every service rate is positive. Excluded: reducible routing
--   - encoding: the steady-state distribution, treated as unique (p. 7) → any probability vector on the finite state space that satisfies the balance equations; reason: the balance equations are the paper’s characterization of stationarity, and quantifying over all laws avoids assuming uniqueness
--   - encoding: n nodes → n ≥ 1 (NeZero n); reason: the maximum over nodes needs a node
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 20 (PDF 21), Lemma 17

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_StationaryLaw
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_TravelTimes

open Finset QueueingFundamentals.Networks

namespace SharedVehicleApprox.Pricing.Supplement

/-- Lemma 17, p. 20 (corrected: the support graph of `q` is strongly connected): with travel times,
if `m ≥ 100` and `∑_{i,j} φ_ij τ_ij q_ij ≤ m − 2 √(m ln m)`, the maximum availability satisfies
`A_m(q) ≥ (1 − 3/√m) (√(m ln m) / (√(m ln m) + n − 1))`. -/
theorem lemma_17 {n m : ℕ} [NeZero n] (hm : 100 ≤ m) (φ τ : Fin n → Fin n → ℝ)
    (hφ : ∀ i j, 0 ≤ φ i j) (hτ : ∀ i j, 0 < τ i j)
    (q : Fin n → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1)
    (hconn : SupportConnected φ q)
    (hload : ∑ i, ∑ j, φ i j * τ i j * q i j ≤ (m : ℝ) - 2 * Real.sqrt (m * Real.log m))
    (π : TTState n → ℝ) (hπ : IsTTStationary n m φ τ (toTTPolicy q) π) :
    (1 - 3 / Real.sqrt m) *
        (Real.sqrt (m * Real.log m) / (Real.sqrt (m * Real.log m) + n - 1)) ≤
      ttMaxAvailability m π := by sorry

end SharedVehicleApprox.Pricing.Supplement
