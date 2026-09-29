-- Prove2me | Theorems.Thm_TongString_virasoro_shapiro_integral
-- name    : TongString.virasoro_shapiro_integral
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T20:56:45.978014+00:00
-- url     : https://prove2.me/theorems/56b68a4c-4ec3-4c39-9858-11797b34a247
-- title:
--   Eq. (6.11): $\int d^2z\,|z|^{2a-2}|1-z|^{2b-2}=\frac{2\pi\Gamma(a)\Gamma(b)\Gamma(c)}{\Gamma(1-a)\Gamma(1-b)\Gamma(1-c)}$
-- statement:
--   Let $a,b,c\in\mathbb C$ with
--
--   $$
--   a+b+c=1,\qquad \operatorname{Re}a>0,\quad \operatorname{Re}b>0,\quad \operatorname{Re}c>0,
--   $$
--
--   and let $C(a,b)=\int_{\mathbb C} d^2z\,|z|^{2a-2}|1-z|^{2b-2}$ with Tong's measure convention $d^2z=2\,dx\,dy$. Then
--
--   $$
--   \int d^2z\;|z|^{2a-2}\,|1-z|^{2b-2}=\frac{2\pi\,\Gamma(a)\,\Gamma(b)\,\Gamma(c)}{\Gamma(1-a)\,\Gamma(1-b)\,\Gamma(1-c)}.
--   $$
--
--   This closed form turns the gauge-fixed closed-string four-tachyon amplitude (6.10) into the Virasoro–Shapiro amplitude (6.12), from which its symmetry in $s,t,u$ and its poles at the closed-string masses are read off.
--
--   **Formalization Note** The three real-part conditions are exactly the conditions for absolute convergence at $z=0$, $z=1$ and $z=\infty$; Tong states only $a+b+c=1$, leaving convergence implicit. The parameters are allowed to be complex; the notes' real exponents are a special case.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 6.2.2, p. 137, eq. (6.11); proof in Appendix 6.5, pp. 157–158

import Mathlib
import Definitions.Def_TongString_vs_integral

namespace TongString

open Complex

theorem virasoro_shapiro_integral (a b c : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re)
    (habc : a + b + c = 1) :
    virasoroShapiroIntegral a b =
      2 * Real.pi * Gamma a * Gamma b * Gamma c /
        (Gamma (1 - a) * Gamma (1 - b) * Gamma (1 - c)) := by sorry

end TongString
