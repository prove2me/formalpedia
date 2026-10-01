-- Prove2me | Theorems.Thm_TongString_vs_integral_change_of_variables
-- name    : TongString.vs_integral_change_of_variables
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T20:55:31.82185+00:00
-- url     : https://prove2.me/theorems/03774b58-0c10-478f-aa2c-2bfb95be0127
-- title:
--   Change of variables $t=\alpha\beta$, $u=(1-\beta)\alpha$
-- statement:
--   Let $a,b\in\mathbb C$ with $\operatorname{Re}a>0$, $\operatorname{Re}b>0$ and $\operatorname{Re}(a+b)<1$. Then
--
--   $$
--   \int_0^\infty dt\int_0^\infty du\;\frac{t^{-a}u^{-b}}{t+u}\,e^{-tu/(t+u)}
--   =\int_0^\infty d\alpha\int_0^1 d\beta\;\alpha^{-a-b}\,\beta^{-a}(1-\beta)^{-b}\,e^{-\alpha\beta(1-\beta)}.
--   $$
--
--   This is the substitution $t=\alpha\beta$, $u=(1-\beta)\alpha$ with $\alpha\in(0,\infty)$, $\beta\in(0,1)$, whose Jacobian is $\alpha$; after it the $\alpha$-integral becomes a Gamma integral.
--
--   **Formalization Note** Both sides are iterated Lebesgue integrals over open intervals, with principal-branch complex powers of positive reals.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Appendix 6.5, p. 158 ('Finally, we make a change of variables. We write t = αβ and u = (1 − β)α ...')

import Mathlib

namespace TongString

open Complex MeasureTheory

theorem vs_integral_change_of_variables (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re)
    (hab : (a + b).re < 1) :
    (∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Ioi (0 : ℝ),
        (t : ℂ) ^ (-a) * (u : ℂ) ^ (-b) / ((t : ℂ) + u) *
          Complex.exp (-((t : ℂ) * u / (t + u)))) =
      ∫ α in Set.Ioi (0 : ℝ), ∫ β in Set.Ioo (0 : ℝ) 1,
        (α : ℂ) ^ (-a - b) * (β : ℂ) ^ (-a) * ((1 - β : ℝ) : ℂ) ^ (-b) *
          Complex.exp (-((α : ℂ) * β * (1 - β))) := by sorry

end TongString
