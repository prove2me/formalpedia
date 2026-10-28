-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_lemma_10
-- name    : SharedVehicleApprox.Pricing.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:22.497562+00:00
-- url     : https://prove2.me/theorems/43cb48e9-0e05-4591-84e3-b3e77e60ebde
-- title:
--   Lemma 10, p. 16 — balanced demand implies equal availabilities at all nodes, for every m and for m = ∞ (corrected: support of q strongly connected)
-- statement:
--   Let $\varphi_{ij}\ge0$ be arrival rates on $n\ge1$ nodes and let $q\in[0,1]^{n\times n}$ be a state-independent quantile matrix with balanced demand, $\sum_k\varphi_{ki}q_{ki}=\sum_j\varphi_{ij}q_{ij}$ for every $i$, whose support graph $\{(a,b):a\ne b,\ \varphi_{ab}q_{ab}>0\}$ is strongly connected. Then
--
--   1. for every $m$ and every stationary law $\pi$ of the $m$-unit system run under $q$, the availabilities $A_{i,m}=\sum_{x\in S_{n,m}}\pi(x)\mathbf 1\{x_i>0\}$ are equal at all nodes;
--   2. for every positive solution $r$ of the traffic equations of $q$, the infinite-unit availabilities $A_{i,\infty}=r_i/\max_jr_j$ are equal at all nodes.
--
--   Combined with Proposition 6 this shows that every node of a balanced policy has infinite-unit availability $1$ (Lemma 11).
--
--   Differences from the source:
--   - correction: no connectivity hypothesis (the proof invokes "the assumption that our system is irreducible (see Appendix A)") → hypothesis SupportConnected φ q; reason: the printed statement is false without it: n = 2, m = 2, φ_ij = 1 for all i, j, q = (q_11, q_12, q_21, q_22) = (1, 0, 0, 1): q is balanced; under q no ride changes the state, so every law on S_{2,2} satisfies (1), and δ_{(2,0)} gives A_1 = 1 ≠ 0 = A_2
--   - encoding: "for any m (including ∞)" → clause 1 for every finite m and every stationary law; clause 2 for A_{i,∞} = r_i/max_j r_j with r any positive traffic solution; reason: the infinite-unit availabilities are r_i/max_j r_j by Proposition 6; under connectivity every positive traffic solution is a multiple of r(q)
--   - encoding: π is the steady-state distribution of the policy, treated as unique (p. 7) → π is any probability vector on S_{n,m}, zero off S_{n,m}, satisfying the balance equation (1) at every state; reason: p. 7: "our upper bounds are all with respect to the best-possible steady-state distribution"; (1) is the paper's characterization of stationarity, and Mathlib has no continuous-time Markov chains
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 16 (PDF 17), Lemma 10

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks Filter Topology

namespace SharedVehicleApprox.Pricing

/-- Lemma 10, p. 16: if a state-independent `q` with strongly connected support satisfies balanced
demand, then (a) for every `m`, every stationary law of the `m`-unit system gives all nodes the
same availability, and (b) the infinite-unit availabilities `r_i / r_max` are all equal. -/
theorem lemma_10 {n : ℕ} [NeZero n] (φ : Fin n → Fin n → ℝ) (hφ : ∀ i j, 0 ≤ φ i j)
    (q : Fin n → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j ∧ q i j ≤ 1) (hbal : IsBalanced φ q)
    (hconn : SupportConnected φ q) :
    (∀ (m : ℕ) (π : (Fin n → ℕ) → ℝ), IsStationary n m φ (toPolicy q) π →
      ∀ i j, availability m π i = availability m π j) ∧
    (∀ r : Fin n → ℝ, (∀ i, 0 < r i) → IsTraffic φ q r →
      ∀ i j, availInf r i = availInf r j) := by sorry

end SharedVehicleApprox.Pricing
