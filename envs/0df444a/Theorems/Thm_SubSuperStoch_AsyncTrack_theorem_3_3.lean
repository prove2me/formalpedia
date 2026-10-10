-- Prove2me | Theorems.Thm_SubSuperStoch_AsyncTrack_theorem_3_3
-- name    : SubSuperStoch.AsyncTrack.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:30.538805+00:00
-- url     : https://prove2.me/theorems/67ed8e1c-8966-4d79-ae90-7a89f8732726
-- title:
--   Theorem 3.3 (sufficiency, the "if" part), p. 16 — ψ < 1/(τd_M), C1 and C2 give asynchronous bipartite tracking
-- statement:
--   This is the sufficiency (the "if" part) of Theorem 3.3.
--
--   Consider a leader $v_0$ with static position $x_0(k+1)=x_0(k)\in\mathbb R^p$ and $n$ followers $v_1,\dots,v_n$ updating by $x_i(k+1)=x_i(k)+\tau u_i(k)$, where $\tau>0$ and the asynchronous protocol (3.3) is
--   $$u_i(k)=\psi\sum_{v_j\in\mathcal N_i}|a_{ij}|\big[\operatorname{sgn}(a_{ij})x_j(k)-x_i(k)\big]+\psi|a_{i0}|\big[\operatorname{sgn}(a_{i0})x_0(k)-x_i(k)\big]$$
--   at the communication instants $s^i_k\tau$ of $v_i$ and $u_i(k)=0$ at all other instants. The instants satisfy $s^i_0=0$, $s^i_k<s^i_{k+1}$ and (2.10) $s^i_{k+1}-s^i_k\le h$ for a constant $h\in\mathbb Z_+$. Let $d_M=\max_i\big(\sum_{v_j\in\mathcal N_i}|a_{ij}|+|a_{i0}|\big)$ and suppose the gain $\psi>0$ satisfies (3.7),
--   $$\psi<\frac{1}{\tau d_M}.$$
--   Suppose further that the signed digraph satisfies
--
--   1. **C1**: it is structurally balanced with respect to a partition $\mathcal V_1\cup\mathcal V_2$ of all agents with $v_0\in\mathcal V_1$;
--   2. **C2**: every follower is reachable from the leader by a directed path.
--
--   Then, for every choice of initial positions, bipartite tracking is achieved (Definition 3.1):
--   $$\lim_{k\to\infty}\|x_i(k)-x_0(k)\|=0\ \ (v_i\in\mathcal V_1),\qquad \lim_{k\to\infty}\|x_i(k)+x_0(k)\|=0\ \ (v_i\in\mathcal V_2).$$
--
--   Followers in the leader's camp converge to the leader's position and followers in the opposing camp converge to its negative, although each follower updates only at its own, unevenly spaced, instants.
--
--   **Formalization Note** Only the "if" direction is stated. Definition 3.1 refers to the partition $\mathcal V_1,\mathcal V_2$ supplied by C1, so the "only if" direction (necessity of C1) has no formal content independent of C1, and the printed necessity argument is an informal case discussion. The partition is given by `V₁` (the followers in $\mathcal V_1$) with the leader fixed in $\mathcal V_1$, as on p. 12. $d_M$ is passed as a value with an `IsGreatest` hypothesis over the printed set; (3.7) is kept in the printed form `ψ < 1 / (τ * dM)`. The norm on $\mathbb R^p$ is the Euclidean norm (the paper leaves it unspecified; all norms give the same limits).
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 16, Theorem 3.3 (sufficiency, proof pp. 16–17, (3.14)); model (3.1)–(3.3) and Definition 3.1, p. 14; (2.10), p. 13; C1, C2, p. 12; (3.7), p. 15

import Mathlib
import Definitions.Def_SubSuperStoch_AsyncTrack_SignedDigraph
import Definitions.Def_SubSuperStoch_AsyncTrack_AsyncModel

namespace SubSuperStoch.AsyncTrack

/-- Theorem 3.3, sufficiency (the "if" part) (p. 16): if the gain satisfies (3.7)
`ψ < 1/(τ d_M)` and the signed digraph satisfies C1 (structural balance, partition
`𝒱₁ = {v₀} ∪ V₁`, `𝒱₂ = Fin n \ V₁`) and C2 (every follower is reachable from the leader), then
every trajectory of the asynchronous system (3.1)–(3.3) realizes bipartite tracking
(Definition 3.1): `x_i(k) − x_0(k) → 0` on `V₁` and `x_i(k) + x_0(k) → 0` off `V₁`. -/
theorem theorem_3_3 {n p : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (τ ψ : ℝ) (hτ : 0 < τ) (hψ : 0 < ψ) (s : Fin n → ℕ → ℕ) (h : ℕ)
    (hs : IsAsyncInstants s h)
    (dM : ℝ) (hdM : IsGreatest {x | ∃ i, x = ∑ j, |a i j| + |b i|} dM)
    (h37 : ψ < 1 / (τ * dM))
    (V₁ : Set (Fin n)) (hC1 : StructBalanced a b V₁) (hC2 : LeaderReachable a b)
    (x0 : ℕ → EuclideanSpace ℝ (Fin p)) (x : Fin n → ℕ → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun a b τ ψ s x0 x) :
    BipartiteTracking V₁ x0 x := by sorry

end SubSuperStoch.AsyncTrack
