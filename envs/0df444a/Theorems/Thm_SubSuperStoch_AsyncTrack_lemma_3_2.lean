-- Prove2me | Theorems.Thm_SubSuperStoch_AsyncTrack_lemma_3_2
-- name    : SubSuperStoch.AsyncTrack.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:44:39.20862+00:00
-- url     : https://prove2.me/theorems/4e6e9357-143d-40c8-8263-6627384ae396
-- title:
--   Lemma 3.2, p. 15 — under (3.7), C1 and C2, ‖∏_{s=k}^{k+Ph−1} M(s)‖_∞ < 1 with P = max_i d(v₀, v_i)
-- statement:
--   Consider the asynchronous leader–follower network with step size $\tau>0$, gain $\psi>0$, and communication instants satisfying (2.10) with constant $h\in\mathbb Z_+$. Suppose the gain satisfies (3.7), $\psi<1/(\tau d_M)$, and the topology satisfies C1 (structural balance, with the leader in $\mathcal V_1$) and C2 (every follower is reachable from the leader). Let
--   $$P=\max\{d(v_0,v_i)\mid i=1,\dots,n\}$$
--   be the largest directed distance from the leader to a follower. Then for every $k\in\mathbb N$,
--   $$\Big\|\prod_{s=k}^{k+Ph-1}M(s)\Big\|_\infty<1,$$
--   where $\prod_{s=k}^{k+Ph-1}M(s)=M(k+Ph-1)\cdots M(k)$.
--
--   Every window of $Ph$ consecutive steps contracts the error, whatever the communication instants. This is what the proof of Theorem 3.3 iterates over consecutive windows.
--
--   **Formalization Note** $d_M$ and $P$ are passed as values with `IsGreatest` hypotheses over exactly the printed sets; $d(v_0,v_i)$ is the least $z$ with `reachWithin a b z i`. The product is `prodFrom (Mmat a b τ ψ s) k (P * h)`. Condition C1 is kept as in the lemma's statement, although the claim does not depend on it.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 15, Lemma 3.2 and (3.8) (proof p. 16, (3.9)–(3.13))

import Mathlib
import Definitions.Def_SubSuperStoch_AsyncTrack_Matrix
import Definitions.Def_SubSuperStoch_AsyncTrack_SignedDigraph
import Definitions.Def_SubSuperStoch_AsyncTrack_AsyncModel

namespace SubSuperStoch.AsyncTrack

/-- Lemma 3.2 (p. 15): under (3.7) and conditions C1, C2, for every `k ∈ ℕ`,
`‖∏_{s=k}^{k+Ph−1} M(s)‖_∞ < 1` (product `M(k+Ph−1) ⋯ M(k)`), where
`P = max_i d(v₀, v_i)` is the largest directed distance from the leader to a follower. -/
theorem lemma_3_2 {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (τ ψ : ℝ) (hτ : 0 < τ) (hψ : 0 < ψ) (s : Fin n → ℕ → ℕ) (h : ℕ)
    (hs : IsAsyncInstants s h)
    (dM : ℝ) (hdM : IsGreatest {x | ∃ i, x = ∑ j, |a i j| + |b i|} dM)
    (h37 : ψ < 1 / (τ * dM))
    (V₁ : Set (Fin n)) (hC1 : StructBalanced a b V₁) (hC2 : LeaderReachable a b)
    (P : ℕ) (hP : IsGreatest {z | ∃ i, IsLeast {m | reachWithin a b m i} z} P) :
    ∀ k, normInf (prodFrom (Mmat a b τ ψ s) k (P * h)) < 1 := by sorry

end SubSuperStoch.AsyncTrack
