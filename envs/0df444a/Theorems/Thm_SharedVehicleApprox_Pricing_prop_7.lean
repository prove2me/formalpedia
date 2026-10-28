-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_prop_7
-- name    : SharedVehicleApprox.Pricing.prop_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:46.369982+00:00
-- url     : https://prove2.me/theorems/f9765000-ddf6-4662-9951-21fcbb0103b9
-- title:
--   Proposition 7, p. 13 — demand bounding: under any state-dependent policy the steady-state flow f_ij,m(q) is at most φ_ij
-- statement:
--   Consider the $m$-unit system with arrival rates $\varphi_{ij}\ge0$, a state-dependent quantile policy $q$ (quantiles $q_{ij}(x)\in[0,1]$, zero when $x_i=0$) and any stationary law $\pi$ of it. Then for all nodes $i,j$ the steady-state flow (3) satisfies the **demand bounding** property
--   $$f_{ij,m}(q)=\sum_{x\in S_{n,m}}\pi(x)\,\varphi_{ij}\,q_{ij}(x)\le\varphi_{ij}.$$
--
--   Together with supply circulation (Proposition 8) this defines the flow polytope behind the elevated flow relaxation of Algorithm 1.
--
--   Differences from the source:
--   - encoding: π is the steady-state distribution of the policy, treated as unique (p. 7) → π is any probability vector on S_{n,m}, zero off S_{n,m}, satisfying the balance equation (1) at every state; reason: p. 7: "our upper bounds are all with respect to the best-possible steady-state distribution"; (1) is the paper's characterization of stationarity, and Mathlib has no continuous-time Markov chains
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 13 (PDF 14), Proposition 7

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks Filter Topology

namespace SharedVehicleApprox.Pricing

/-- Proposition 7 (demand bounding), p. 13: under any state-dependent policy `q` and any
stationary law `π` of it, the steady-state flow satisfies `f_ij,m(q) ≤ φ_ij`. -/
theorem prop_7 {n m : ℕ} (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ)
    (hq : IsPolicy n m q) (hπ : IsStationary n m φ q π) (i j : Fin n) :
    flow n m φ q π i j ≤ φ i j := by sorry

end SharedVehicleApprox.Pricing
