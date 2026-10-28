-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_prop_8
-- name    : SharedVehicleApprox.Pricing.prop_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:43.808777+00:00
-- url     : https://prove2.me/theorems/de2ccbcb-eeb1-419d-8cbb-65fd37301e44
-- title:
--   Proposition 8, p. 13 — supply circulation: steady-state flows are conserved at every node, in the m-unit and in the infinite-unit system
-- statement:
--   Let $\varphi_{ij}\ge0$ be arrival rates on $n\ge1$ nodes.
--
--   1. For every state-dependent quantile policy $q$ of the $m$-unit system and every stationary law $\pi$ of it, the steady-state flows (3) obey flow conservation at every node $i$:
--   $$\sum_k f_{ki,m}(q)=\sum_j f_{ij,m}(q).$$
--   2. For every state-independent quantile matrix $q\in[0,1]^{n\times n}$ and every solution $r\ge0$, $r\ne0$, of its traffic equations $\sum_j r_j\varphi_{ji}q_{ji}=r_i\sum_k\varphi_{ik}q_{ik}$, the infinite-unit flows $A_{i,\infty}\varphi_{ij}q_{ij}$, with $A_{i,\infty}=r_i/\max_j r_j$, are conserved at every node:
--   $$\sum_k A_{k,\infty}\varphi_{ki}q_{ki}=\sum_j A_{i,\infty}\varphi_{ij}q_{ij}.$$
--
--   Part 1 is the reason the averaged quantiles of any state-dependent policy are feasible for the elevated flow relaxation (Lemma 9).
--
--   Differences from the source:
--   - encoding: π is the steady-state distribution of the policy, treated as unique (p. 7) → π is any probability vector on S_{n,m}, zero off S_{n,m}, satisfying the balance equation (1) at every state; reason: p. 7: "our upper bounds are all with respect to the best-possible steady-state distribution"; (1) is the paper's characterization of stationarity, and Mathlib has no continuous-time Markov chains
--   - encoding: flows "in the infinite-unit system" → A_{i,∞} φ_ij q_ij with A_{i,∞} = r_i / max_j r_j; reason: Proposition 6 (p. 12) gives the infinite-unit availabilities as r_i/max_j r_j, and the proof of Proposition 8 (p. 14) uses exactly these flows
--   - generalization: r = r(q) = w(q)/µ(q), the traffic intensities of q → any solution r ≥ 0 with some r_j > 0 of the rate-form traffic equations; reason: the proof of Proposition 8 (p. 14) shows r(q) solves these equations, and r(q) = w/µ is nonnegative with a positive entry (w an invariant distribution, possibly with zero entries when P(q) is reducible), so the statement specializes to r(q)
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 13 (PDF 14), Proposition 8; proof pp. 13–14 (PDF 14–15)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks Filter Topology

namespace SharedVehicleApprox.Pricing

/-- Proposition 8 (supply circulation), p. 13: (a) under any state-dependent policy `q` and any
stationary law `π` of the `m`-unit system, `∑_k f_ki,m(q) = ∑_j f_ij,m(q)` at every node `i`;
(b) for a state-independent `q` and a nonnegative, nonzero solution `r` of its traffic equations, the
infinite-unit flows `A_i,∞ φ_ij q_ij` with `A_i,∞ = r_i / r_max` are conserved at every node. -/
theorem prop_8 {n m : ℕ} [NeZero n] (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j) :
    (∀ (q : (Fin n → ℕ) → Fin n → Fin n → ℝ) (π : (Fin n → ℕ) → ℝ),
      IsPolicy n m q → IsStationary n m φ q π →
        ∀ i, ∑ k, flow n m φ q π k i = ∑ j, flow n m φ q π i j) ∧
    (∀ (q : Fin n → Fin n → ℝ) (r : Fin n → ℝ),
      (∀ i j, 0 ≤ q i j ∧ q i j ≤ 1) → (∀ i, 0 ≤ r i) → (∃ j, 0 < r j) → IsTraffic φ q r →
        ∀ i, ∑ k, availInf r k * φ k i * q k i = ∑ j, availInf r i * φ i j * q i j) := by sorry

end SharedVehicleApprox.Pricing
