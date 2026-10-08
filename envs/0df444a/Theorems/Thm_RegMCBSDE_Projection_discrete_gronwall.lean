-- Prove2me | Theorems.Thm_RegMCBSDE_Projection_discrete_gronwall
-- name    : RegMCBSDE.Projection.discrete_gronwall
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:20.278427+00:00
-- url     : https://prove2.me/theorems/0e3ba764-6ae8-4922-8325-c1c8f1d6f06f
-- title:
--   Proof of Theorem 2, p. 11, item 3 — the backward discrete Gronwall lemma with c-terms
-- statement:
--   Let $T>0$, $N\ge1$, $h=T/N$, $t_k=kh$ and $\gamma>0$. Let $(a_k)_{0\le k\le N}$, $(b_k)_{0\le k\le N}$ and $(c_k)_{0\le k\le N}$ be nonnegative sequences satisfying
--   $$a_{k-1}+c_{k-1}\le(1+\gamma h)\,a_k+b_{k-1}\qquad(1\le k\le N).$$
--   Then for every $0\le k\le N$,
--   $$a_k+\sum_{i=k}^{N-1}c_i\le e^{\gamma(T-t_k)}\Big[a_N+\sum_{i=k}^{N-1}b_i\Big].$$
--
--   This inequality turns every one-step backward recursion of the error analysis into a global bound whose constant does not grow with $N$; it is used throughout the proof of Theorem 2, most of the time with $c_i=0$.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, p. 11, Proof of Theorem 2, item 3 (the discrete Gronwall lemma)

import Mathlib

namespace RegMCBSDE.Projection

/-- **The discrete Gronwall lemma** (Proof of Theorem 2, p. 11, item 3,
arXiv:math/0508491v1). Let `T > 0`, `N ≥ 1`, `h = T/N`, `t_k = k h` and `γ > 0`. For nonnegative
sequences `(a_k)`, `(b_k)`, `(c_k)` (`0 ≤ k ≤ N`) with
`a_{k-1} + c_{k-1} ≤ (1 + γ h) a_k + b_{k-1}` for `1 ≤ k ≤ N`, one has, for every `0 ≤ k ≤ N`,
`a_k + ∑_{i=k}^{N-1} c_i ≤ e^{γ(T - t_k)} [a_N + ∑_{i=k}^{N-1} b_i]`. -/
theorem discrete_gronwall (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 0 < N) (γ : ℝ) (hγ : 0 < γ)
    (a b c : ℕ → ℝ) (ha : ∀ k ≤ N, 0 ≤ a k) (hb : ∀ k ≤ N, 0 ≤ b k) (hc : ∀ k ≤ N, 0 ≤ c k)
    (hrec : ∀ k, 1 ≤ k → k ≤ N →
      a (k - 1) + c (k - 1) ≤ (1 + γ * (T / N)) * a k + b (k - 1)) :
    ∀ k ≤ N, a k + ∑ i ∈ Finset.Ico k N, c i
      ≤ Real.exp (γ * (T - (k : ℝ) * (T / N))) * (a N + ∑ i ∈ Finset.Ico k N, b i) := by sorry

end RegMCBSDE.Projection
