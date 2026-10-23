-- Prove2me | Theorems.Thm_QuadMemory_ConvexOpt_lemma_13
-- name    : QuadMemory.ConvexOpt.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:49.515983+00:00
-- url     : https://prove2.me/theorems/ffc97386-ba27-4d2b-b67e-b151c155224f
-- title:
--   Lemma 13, p. 22 — a uniform unit vector is d^{−3}-orthogonal to k ≤ d−2 orthonormal vectors with probability ≥ 1/(e^{d^{−4}} d^{3k})
-- statement:
--   Let $k\le d-2$ and let $x_1,\dots,x_k\in\mathbb R^d$ be orthonormal. Then
--   $$\mathbb P_{y\sim\mathcal U(S^{d-1})}\Big(|x_i^\top y|\le\frac1{d^3}\ \text{for all }i\le k\Big)\ge\frac1{e^{d^{-4}}d^{3k}}.$$
--
--   The slab from which each hint is drawn has probability at least $d^{-3k}e^{-d^{-4}}$, so a hint carries at most about $3k\log d$ bits of information about the queries that defined it; this is the anti-concentration half of the information-leakage bound in Proposition 14.
--
--   **Formalization Note.** The page assumes $k<d$. At $k=d-1$ the bound is false (at $d=2$, $k=1$ the probability is $0.080$ against the bound $0.117$): the proof's coordinate density exponent should be $(d-i-2)/2$, which turns negative at $i=d-1$. The statement is restricted to $k\le d-2$; the paper uses it with $k\le d/3-1$.
-- source:
--   Blanchard, Zhang & Jaillet, arXiv:2302.04963v2, p. 22, Lemma 13 (proof pp. 22–23), restricted to k ≤ d − 2

import Mathlib
import Definitions.Def_QuadMemory_ConvexOpt_Model
import Definitions.Def_QuadMemory_ConvexOpt_Game

open MeasureTheory
open scoped RealInnerProductSpace

namespace QuadMemory.ConvexOpt

/-- Lemma 13 (p. 22), for `k ≤ d - 2`: if `x_1, …, x_k` are orthonormal in `ℝ^d` then
`P_{y ∼ U(S^{d-1})}(|x_iᵀ y| ≤ 1/d³ for all i ≤ k) ≥ 1/(e^{d^{-4}} d^{3k})`. The page assumes
`k < d`; at `k = d - 1` the bound fails (`d = 2`: `0.080 < 0.117`). -/
theorem lemma_13 (d k : ℕ) (hk : k + 2 ≤ d) (xs : Fin k → E d) (hxs : Orthonormal ℝ xs) :
    ENNReal.ofReal (1 / (Real.exp (((d : ℝ) ^ 4)⁻¹) * (d : ℝ) ^ (3 * k))) ≤
      sphereLaw d {y | ∀ i, |⟪xs i, y⟫| ≤ 1 / (d : ℝ) ^ 3} := by sorry

end QuadMemory.ConvexOpt
