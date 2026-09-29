-- Prove2me | Theorems.Thm_TongString_vs_integral_gaussian_reduction
-- name    : TongString.vs_integral_gaussian_reduction
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T20:54:59.329818+00:00
-- url     : https://prove2.me/theorems/bd711784-997d-42ea-92aa-84664fda8ab7
-- title:
--   Gaussian reduction of $C(a,b)$ to a double integral over $t,u>0$
-- statement:
--   Let $a,b\in\mathbb C$ satisfy $\operatorname{Re}a>0$, $\operatorname{Re}b>0$ and $\operatorname{Re}(a+b)<1$, and let $C(a,b)=\int d^2z\,|z|^{2a-2}|1-z|^{2b-2}$ be the Virasoro–Shapiro integral (with $d^2z=2\,dx\,dy$). Then
--
--   $$
--   C(a,b)=\frac{2\pi}{\Gamma(1-a)\,\Gamma(1-b)}\int_0^\infty dt\int_0^\infty du\;\frac{t^{-a}\,u^{-b}}{t+u}\;e^{-tu/(t+u)}.
--   $$
--
--   This is the result of inserting the Gamma-function representations of $|z|^{2a-2}$ and $|1-z|^{2b-2}$ and performing the resulting two-dimensional Gaussian integral over $z=x+iy$.
--
--   **Formalization Note** The right-hand side is an iterated integral over $(0,\infty)$ (outer variable $t$, inner variable $u$) with principal-branch complex powers of positive reals.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Appendix 6.5, p. 158 (display after 'Now we do the dxdy integral which is simply Gaussian')

import Mathlib
import Definitions.Def_TongString_vs_integral

namespace TongString

open Complex MeasureTheory

theorem vs_integral_gaussian_reduction (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re)
    (hab : (a + b).re < 1) :
    virasoroShapiroIntegral a b =
      2 * Real.pi / (Gamma (1 - a) * Gamma (1 - b)) *
        ∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Ioi (0 : ℝ),
          (t : ℂ) ^ (-a) * (u : ℂ) ^ (-b) / ((t : ℂ) + u) *
            Complex.exp (-((t : ℂ) * u / (t + u))) := by sorry

end TongString
