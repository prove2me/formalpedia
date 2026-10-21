-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P21_conjugate_rectangle_unique
-- name    : QAlgorithms.Papers.Independent.Next46.P21.conjugate_rectangle_unique
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:36:11.981995+00:00
-- url     : https://prove2.me/theorems/02f5aa1a-7e13-4bbf-b953-854fdf1a8acd
-- title:
--   Uniqueness in a conjugate rectangle
-- statement:
--   Let $x_0<x_1$ and $y_0<y_1$ be real endpoints, and put $\delta=x_1-x_0$ and $\Delta=y_1-y_0$. Let $F$ be the set of quadratic integers $\alpha=a+b\sqrt2$, where $a,b\in\mathbb Z$, satisfying both closed interval constraints. If $\delta\Delta<1$, then
--
--   $$
--   \#F\le1,\qquad F=\{\alpha\in\mathbb Z[\sqrt2]:\alpha\in[x_0,x_1],\ \alpha^\bullet\in[y_0,y_1]\}.
--   $$
--
--   Here $\alpha^\bullet=a-b\sqrt2$. The conclusion asserts uniqueness without asserting existence.
-- source:
--   Efficient Clifford+T approximation of single-qubit operators, arXiv:1212.6253v2, PDF p. 6, Lemma 16: uniqueness in a conjugate rectangle

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P21

open Set

open scoped ComplexConjugate

/-- Lemma 16, PDF p.6: uniqueness only, with the strict endpoint ordering from (16). -/
theorem conjugate_rectangle_unique (x0 x1 y0 y1 : ℝ)
    (hx : x0 < x1) (hy : y0 < y1)
    (harea : (x1 - x0) * (y1 - y0) < 1) :
    (rectangleSolutions x0 x1 y0 y1).Subsingleton := by sorry

end QAlgorithms.Papers.Independent.Next46.P21

end
