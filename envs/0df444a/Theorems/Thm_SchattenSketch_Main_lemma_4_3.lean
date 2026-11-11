-- Prove2me | Theorems.Thm_SchattenSketch_Main_lemma_4_3
-- name    : SchattenSketch.Main.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:56:41.951222+00:00
-- url     : https://prove2.me/theorems/645fefb9-fa0c-444e-b357-0c9e79b8c865
-- title:
--   Lemma 4.3 — Steinitz rearrangement [GS80]: zero-sum vectors of norm $\le 1$ in a $d$-dimensional normed space have an ordering with all partial sums of norm $\le d$
-- statement:
--   Let $d,N\ge 1$, let $\|\cdot\|$ be any norm on $\mathbb R^d$, and let $v_1,\dots,v_N\in\mathbb R^d$ satisfy $\|v_i\|\le 1$ for all $i$ and $\sum_{i=1}^N v_i=0$. Then there is a permutation $\pi$ of $\{1,\dots,N\}$ such that
--   $$\Bigl\|\sum_{i=1}^m v_{\pi(i)}\Bigr\|\le d\qquad(1\le m\le N).$$
--
--   This is the Grinberg–Sevast'yanov form of the Steinitz lemma, cited by the paper; it orders the particle moves in the construction of Lemma 4.4 so that the accumulated moment error stays bounded.
--
--   **Formalization Note.** "Any norm on $\mathbb R^d$" is any real finite-dimensional normed space `E` with `finrank ℝ E = d`. The permutation is `π : Equiv.Perm (Fin N)` and the $m$-th partial sum runs over the 0-based positions $i<m$.
--
--   Differences from the source:
--   - encoding: any norm on R^d → any finite-dimensional real normed space E with finrank ℝ E = d; reason: every such E is linearly isometric to R^d with some norm, and R^d with any norm is such an E
--   - encoding: a permutation π of {1, …, N}; partial sums over i = 1, …, m → π : Equiv.Perm (Fin N); sum over 0-based positions i < m; reason: Lean indexing
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 16, Lemma 4.3 ([GS80, Theorem 1])

import Mathlib

namespace SchattenSketch.Main

/-- Lemma 4.3 (Steinitz rearrangement lemma [GS80, Theorem 1]; Yang, p. 16). In a real normed
space `E` of dimension `d ≥ 1` (any norm), `N ≥ 1` vectors of norm at most one summing to zero
can be ordered so that every partial sum of the first `m` reordered vectors, `1 ≤ m ≤ N`, has
norm at most `d`. -/
theorem lemma_4_3 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (d N : ℕ) (hd : 1 ≤ d) (hE : Module.finrank ℝ E = d) (hN : 1 ≤ N)
    (v : Fin N → E) (hv : ∀ i, ‖v i‖ ≤ 1) (hsum : ∑ i, v i = 0) :
    ∃ π : Equiv.Perm (Fin N), ∀ m : ℕ, 1 ≤ m → m ≤ N →
      ‖∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < m), v (π i)‖ ≤ d := by sorry

end SchattenSketch.Main
