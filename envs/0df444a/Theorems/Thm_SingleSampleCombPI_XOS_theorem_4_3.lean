-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_theorem_4_3
-- name    : SingleSampleCombPI.XOS.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:09:34.185812+00:00
-- url     : https://prove2.me/theorems/179d4962-d6f4-4978-bce5-8f1c5e3157e5
-- title:
--   Theorem 4.3 — random-order greedy over a partition matroid is 0.5096-competitive
-- statement:
--   Let $N$ be a finite ground set partitioned into nonempty pairwise disjoint parts $P_1,\dots,P_\ell$, and let $f:2^N\to\mathbb R_{\ge0}$ be nonnegative, monotone and submodular. The parts are revealed in the order of a uniformly random permutation $\pi$ of $[\ell]$, and on seeing $P_{\pi(t)}$ greedy irrevocably picks $u_t\in\arg\max_{u\in P_{\pi(t)}}f(u\mid A_{t-1})$, $A_t=A_{t-1}\cup\{u_t\}$, $A_0=\emptyset$, with ties broken arbitrarily. Then
--   $$\mathbb E_\pi\big[f(A_\ell)\big]\ \ge\ 0.5096\cdot\max_{S\subseteq N,\ |S\cap P_i|\le1}f(S).$$
--
--   This is the random-order online submodular maximization bound used for Algorithm 4.
--
--   Differences from the source:
--   - reading: ties are broken arbitrarily → any online tie-breaking rule mapping the history of processed parts and the arriving part to a greedy choice; reason: the algorithm is online, so a tie may depend on the past but not on future arrivals; randomized tie-breaking is a mixture of such rules
--   - encoding: 0.5096 → 637/1250; reason: the same exact decimal
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, printed p. 18 / PDF p. 20, Theorem 4.3 (from Buchbinder–Feldman–Filmus–Garg 2020, Theorem 1)

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_PartitionGreedy
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular

namespace SingleSampleCombPI.XOS

/-- **Theorem 4.3** (Chawla–Dang, STOC 2027 submission #30, printed p. 18 / PDF p. 20; from
[BFFG20, Theorem 1]).  For a nonnegative monotone submodular `f` on a finite ground set
partitioned into nonempty pairwise disjoint parts, greedy over the parts in a uniformly random
order, with ties broken arbitrarily (any history-dependent rule), satisfies
`E_π[f(A_ℓ)] ≥ 0.5096 · max_{|S ∩ P_i| ≤ 1} f(S)`. -/
theorem theorem_4_3 {N : Type*} [Fintype N] [DecidableEq N] {ℓ : ℕ} (P : Fin ℓ → Finset N)
    (hP : IsPartition P) (f : Finset N → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hmono : SetMonotone f)
    (hsub : SubsamplingSM.Offline.IsSubmodular f) (rule : List (Fin ℓ) → Fin ℓ → N)
    (hrule : IsApproxGreedyRule f P 0 rule) :
    (637 / 1250 : ℝ) * optVal f P ≤
      avgR (fun π : Equiv.Perm (Fin ℓ) => f (chosen rule (arrivalList (fun _ => true) π))) := by sorry

end SingleSampleCombPI.XOS
