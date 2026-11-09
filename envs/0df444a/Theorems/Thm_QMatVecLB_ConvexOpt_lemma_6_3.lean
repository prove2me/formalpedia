-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_lemma_6_3
-- name    : QMatVecLB.ConvexOpt.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:21:55.123201+00:00
-- url     : https://prove2.me/theorems/4eff29bc-e917-455e-a53e-56bb7189b6f2
-- title:
--   Lemma 6.3 — Cayley operator on an inverse bilinear form
-- statement:
--   Let $n\ge1$, $u,v\in\mathbb R^n$, and $s(B)=u^TB^{-1}v$. Let $h:\mathbb R\to\mathbb R$ extend to an entire function on $\mathbb C$. At every invertible real matrix $B$,
--
--   $$\det(B)\det(\partial_B)\bigl[h(s(B))\bigr]=-(n-1)!s(B)h'(s(B)).$$
--
--   The entire extension agrees with $h$ on every real argument. This identity reduces a matrix differential expression to an ordinary scalar derivative.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
--   - encoding: positive matrix dimension in the inversion section → 1 <= n; reason: the inversion section concerns a nonempty interior block; at n=0 the factorial formula of Lemma 6.3 is not valid
--   - encoding: h extends to an entire function → there exists a complex-differentiable function on all of C whose restriction to R is h; reason: this is the definition of an entire extension; the matrix inverse is used only at an explicitly invertible point
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 6.3, PDF p. 19 (printed p. 18).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Inversion

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem lemma_6_3 (n : ℕ) (hn : 1 ≤ n) (u v : Fin n → ℝ)
    (h : ℝ → ℝ) (hh : ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ x : ℝ, H x = (h x : ℂ))
    (B : RMat n) (hB : B.det ≠ 0) :
    B.det * cayley (fun X => h (schurScalar u v X)) B =
      -(((n-1).factorial : ℝ) * schurScalar u v B * deriv h (schurScalar u v B)) := by sorry

end QMatVecLB.ConvexOpt
