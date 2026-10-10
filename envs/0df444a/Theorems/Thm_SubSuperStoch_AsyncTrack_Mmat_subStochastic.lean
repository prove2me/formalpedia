-- Prove2me | Theorems.Thm_SubSuperStoch_AsyncTrack_Mmat_subStochastic
-- name    : SubSuperStoch.AsyncTrack.Mmat_subStochastic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:03.171147+00:00
-- url     : https://prove2.me/theorems/6c9e9aa9-d72a-47a3-b966-f814ea29b9fe
-- title:
--   §3, p. 15 — under ψ < 1/(τd_M) every M(k) is sub-stochastic with positive diagonal; Λ_i[M(k)] < 1 iff (v₀, v_i) ∈ ℰ̃(k)
-- statement:
--   Consider the asynchronous leader–follower network with step size $\tau>0$, gain $\psi>0$, follower weights $a_{ij}$ and leader weights $a_{i0}$. Let
--   $$d_M=\max\Big\{\sum_{v_j\in\mathcal N_i}|a_{ij}|+|a_{i0}|\ \Big|\ i=1,\dots,n\Big\}$$
--   be the largest total absolute weight received by a follower, and suppose the gain satisfies (3.7),
--   $$\psi<\frac{1}{\tau d_M}.$$
--   Then for every $k\in\mathbb N$ the matrix $M(k)=I_n-\tau\psi\mathcal D(k)-\tau\psi\mathcal B(k)+\tau\psi|\mathcal A(k)|$ is sub-stochastic, its diagonal entries are positive, and its row sums satisfy
--   $$\Lambda_i[M(k)]<1\ \text{ if } (v_0,v_i)\in\tilde{\mathcal E}(k),\qquad \Lambda_i[M(k)]=1\ \text{ if } (v_0,v_i)\notin\tilde{\mathcal E}(k),$$
--   for $i=1,\dots,n$. Here the leader edge $(v_0,v_i)$ is present at time $k\tau$ exactly when $a_{i0}(k)\neq 0$, that is, when $k\tau$ is a communication instant of $v_i$ and $a_{i0}\neq 0$.
--
--   This turns the tracking question into one about products of sub-stochastic matrices: the error system (3.6) is driven by the matrices $M(k)$, and only the rows of followers that hear the leader at time $k\tau$ lose mass.
--
--   **Formalization Note** $d_M$ is passed as a value with an `IsGreatest` hypothesis over exactly the printed set (the sum over $\mathcal N_i$ equals the sum over all $j$, since the other terms vanish). (3.7) is kept in the printed form `ψ < 1 / (τ * dM)`; in Lean $1/0=0$, so if $d_M=0$ the hypothesis contradicts $\psi>0$. The asynchronous-instant condition (2.10) is not assumed: the claim holds for any choice of instants.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 15, (3.7) and the claim following it on the matrices M(k)

import Mathlib
import Definitions.Def_SubSuperStoch_AsyncTrack_Matrix
import Definitions.Def_SubSuperStoch_AsyncTrack_AsyncModel

namespace SubSuperStoch.AsyncTrack

/-- §3, p. 15: under the gain bound (3.7) `ψ < 1/(τ d_M)`, with
`d_M = max_i (∑_{v_j ∈ 𝒩_i} |a_ij| + |a_i0|)`, every `M(k)` is sub-stochastic with positive diagonal
entries, and `Λ_i[M(k)] < 1` if the leader edge `(v₀, v_i)` is present at time `kτ` (follower `i`
communicates at `kτ` and `a_i0 ≠ 0`), while `Λ_i[M(k)] = 1` otherwise. -/
theorem Mmat_subStochastic {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (τ ψ : ℝ) (hτ : 0 < τ) (hψ : 0 < ψ) (s : Fin n → ℕ → ℕ)
    (dM : ℝ) (hdM : IsGreatest {x | ∃ i, x = ∑ j, |a i j| + |b i|} dM)
    (h37 : ψ < 1 / (τ * dM)) :
    ∀ k, IsSubStochastic (Mmat a b τ ψ s k) ∧ (∀ i, 0 < Mmat a b τ ψ s k i i) ∧
      ∀ i, ((active s i k ∧ b i ≠ 0) → rowSum (Mmat a b τ ψ s k) i < 1) ∧
        (¬(active s i k ∧ b i ≠ 0) → rowSum (Mmat a b τ ψ s k) i = 1) := by sorry

end SubSuperStoch.AsyncTrack
