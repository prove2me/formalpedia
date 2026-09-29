-- Prove2me | Theorems.Thm_TwoChartCech_finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1
-- name    : TwoChartCech.finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/744c2a90-aac1-5f6e-b31e-ae801271ff3f
-- title:
--   Čech cohomology of glued lines in multidegree (s-1,0)
-- statement:
--   Let $k$ be a field, let $s$ be a natural number, and let $a, b, \lambda : \mathrm{Fin}\,s \to k^{\times}$ be families of units, with $a$ injective. Consider the two-chart Čech datum `gluedLinesSections k a b lam ((s : ℤ) - 1) 0` over the cover `gluedLinesCover k a b`: its module of sections on the overlap is the set `gluedLinesM01` of pairs $(f_1,f_2)$ of Laurent polynomials over $k$ satisfying the gluing predicate `GluedCond a b lam` attached to the data $a$, $b$, $\lambda$; the module on the first chart is `gluedLinesM0`, the pairs satisfying `GluedCond a b lam` whose two components lie in the subalgebra `polyPart k`; and the module on the second chart is `gluedLinesM1 k a b lam ((s : ℤ) - 1) 0`, the pairs satisfying `GluedCond a b lam` for which $f_1 \cdot T^{-(s-1)}$ and $f_2 \cdot T^{0}$ lie in `invPolyPart k`. The Čech differential is the $k$-linear map $(u,v) \mapsto -u + v$ from the product of the two chart modules to the overlap module, given by the respective inclusions. The assertion is twofold: its kernel, the module $H^0$, has $k$-dimension exactly $1$, and the quotient of the overlap module by its image, the module $H^1$, is a subsingleton, i.e. zero.
--
--   This is the cohomology computation for the line bundle of multidegree $(s-1,0)$, with gluing constants $\lambda_i$, on the curve obtained by identifying the points $x = a_i$ and $y = b_i$ of two projective lines, expressed purely in terms of Laurent polynomials and a two-chart Čech complex. It is the input to the results on two glued projective lines that compare $H^0$ of twists with Euler characteristics and with the triviality of pullbacks, such as [`AlgebraicGeometry.TwoGluedProjectiveLines.finrank_H0_sectionsOf_eq_one_and_subsingleton_H1_of_eulerChar_pullback_eq_of_isAlgClosed`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.finrank_H0_sectionsOf_eq_one_and_subsingleton_H1_of_eulerChar_pullback_eq_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwoChartCech_finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1.lean

import Mathlib
import Definitions.Def_TwoChartCech_GluedLines

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TwoChartCech

universe u

theorem TwoChartCech.finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1
    (k : Type u) [Field k] {s : ℕ} (a b lam : Fin s → kˣ) (ha : Function.Injective a) :
    Module.finrank k ↥(gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H0 = 1 ∧
      Subsingleton (gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H1 := by sorry
