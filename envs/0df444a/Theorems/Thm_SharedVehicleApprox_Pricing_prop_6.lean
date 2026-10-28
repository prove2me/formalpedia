-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_prop_6
-- name    : SharedVehicleApprox.Pricing.prop_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:12.189872+00:00
-- url     : https://prove2.me/theorems/325a406a-99bb-4180-9ebe-ebe508c16a88
-- title:
--   Proposition 6, p. 12 — infinite-unit availability of node i is r_i(q)/max_j r_j(q) (corrected: support of q strongly connected)
-- statement:
--   Let $\varphi_{ij}\ge0$ be arrival rates on $n\ge1$ nodes and $q\in[0,1]^{n\times n}$ a state-independent quantile matrix whose support graph $\{(a,b):a\ne b,\ \varphi_{ab}q_{ab}>0\}$ is strongly connected. Let $r$ be a positive solution of the traffic equations $\sum_jr_j\varphi_{ji}q_{ji}=r_i\sum_k\varphi_{ik}q_{ik}$ (it does not depend on $m$), and for every $m$ let $\pi_m$ be a stationary law of the $m$-unit system run under $q$. Then for every node $i$
--   $$\lim_{m\to\infty}A_{i,m}=\frac{r_i}{\max_jr_j},\qquad A_{i,m}=\sum_{x\in S_{n,m}}\pi_m(x)\mathbf 1\{x_i>0\}.$$
--
--   These limits are the infinite-unit availabilities $A_{i,\infty}$ used in Lemmas 10–12.
--
--   Differences from the source:
--   - correction: no connectivity hypothesis; w(q) "the" invariant distribution of P(q) → hypothesis SupportConnected φ q; reason: the paper's standing irreducibility assumption (p. 7, App. A). Without it the statement is false: n = 2, φ ≡ 1, q = (1, 0, 0, 1); then P = I, w = (1/3, 2/3) is an invariant distribution, r = w/µ = (1/3, 2/3), and the stationary laws δ_{(m,0)} give A_{2,m} = 0 for every m, while r_2/max r = 1
--   - generalization: r = r(q) = w(q)/µ(q) → any positive solution r of the rate-form traffic equations; reason: r(q) is such a solution (proof of Proposition 8, p. 14), so the statement specializes to it
--   - encoding: "in the infinite-unit limit" with "the" steady-state distribution (4) → Tendsto as m → ∞ of the availability under any family of stationary laws π_m of toPolicy q; reason: p. 12: "as m → ∞"; under the connectivity hypothesis the stationary law is unique, and quantifying over all laws avoids assuming it
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 12 (PDF 13), Proposition 6

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks Filter Topology

namespace SharedVehicleApprox.Pricing

/-- Proposition 6, p. 12: for a state-independent `q` with strongly connected support and a
positive solution `r` of its traffic equations, the availability of node `i` under the stationary
law of the `m`-unit system tends to `r_i / max_j r_j` as `m → ∞`. -/
theorem prop_6 {n : ℕ} [NeZero n] (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (q : Fin n → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1) (hconn : SupportConnected φ q)
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (htr : IsTraffic φ q r)
    (πs : ℕ → (Fin n → ℕ) → ℝ) (hπs : ∀ m, IsStationary n m φ (toPolicy q) (πs m))
    (i : Fin n) :
    Tendsto (fun m => availability m (πs m) i) atTop (𝓝 (availInf r i)) := by sorry

end SharedVehicleApprox.Pricing
