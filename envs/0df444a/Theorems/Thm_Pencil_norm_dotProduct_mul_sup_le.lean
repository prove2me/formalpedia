-- Prove2me | Theorems.Thm_Pencil_norm_dotProduct_mul_sup_le
-- name    : Pencil.norm_dotProduct_mul_sup_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/0bd8770b-7d88-500e-a040-f757d98cd59a
-- title:
--   Orthogonal covector bound by the 2×2 minors of v,w
-- statement:
--   Let $r$ be a natural number and let $a,v,w\colon \mathrm{Fin}\,r \to \mathbb{C}$ be three families of complex numbers indexed by $\{0,\dots,r-1\}$, subject to the single hypothesis that $a$ is orthogonal to $v$ in the bilinear (not Hermitian) sense, i.e. $\sum_i a_i v_i = 0$. The assertion is the inequality of real numbers
--   $$\Bigl\lVert \sum_i a_i w_i \Bigr\rVert \cdot \Bigl(\sup_i \lVert v_i\rVert\Bigr) \le \Bigl(\sum_i \lVert a_i\rVert\Bigr) \cdot \sup_{(p_1,p_2)} \lVert v_{p_1} w_{p_2} - v_{p_2} w_{p_1}\rVert,$$
--   where $\lVert \cdot \rVert$ is the complex absolute value, the first supremum is the conditionally complete supremum of $i \mapsto \lVert v_i\rVert$ over $\mathrm{Fin}\,r$, and the second is taken over all pairs $p \in \mathrm{Fin}\,r \times \mathrm{Fin}\,r$ of the absolute values of the $2\times 2$ minors $v_{p_1} w_{p_2} - v_{p_2} w_{p_1}$. Thus the value of the linear form $a$ at $w$, scaled by the sup-norm of $v$, is bounded by the $\ell^1$-norm of $a$ times the sup-norm of $v \wedge w$. For $r = 0$ all sums are empty and both suprema are suprema over an empty index type, so the inequality holds in the degenerate form $0 \le 0$.
--
--   This is the elementary pointwise half of the comparison between the Chow-form size $\lvert a \cdot w\rvert$ for covectors $a$ annihilating $v$ and the chordal proximity of the points $[v], [w] \in \mathbb{P}^{r-1}(\mathbb{C})$ measured by the minors $v_i w_j - v_j w_i$: a covector through $[v]$ takes small values at $w$ when $[w]$ is close to $[v]$. It is used in the estimate [`ModularCurve.JZero.prox_sum_chowSide`](thm.html#ModularCurve.JZero.prox_sum_chowSide).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Pencil_norm_dotProduct_mul_sup_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Pencil.norm_dotProduct_mul_sup_le {r : ℕ} (a v w : Fin r → ℂ) (hav : ∑ i, a i * v i = 0) :
    ‖∑ i, a i * w i‖ * (⨆ i, ‖v i‖)
      ≤ (∑ i, ‖a i‖) * ⨆ p : Fin r × Fin r, ‖v p.1 * w p.2 - v p.2 * w p.1‖ := by sorry
