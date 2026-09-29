-- Prove2me | Theorems.Thm_TongString_vs_integral_beta_form
-- name    : TongString.vs_integral_beta_form
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T20:56:19.382168+00:00
-- url     : https://prove2.me/theorems/f8959ea6-33a5-44da-abdf-7a86220c9d22
-- title:
--   $C(a,b)=\frac{2\pi\Gamma(c)}{\Gamma(1-a)\Gamma(1-b)}\int_0^1 d\beta\,(1-\beta)^{a-1}\beta^{b-1}$
-- statement:
--   Let $a,b,c\in\mathbb C$ with $a+b+c=1$ and $\operatorname{Re}a,\operatorname{Re}b,\operatorname{Re}c>0$, and let $C(a,b)=\int d^2z\,|z|^{2a-2}|1-z|^{2b-2}$ be the Virasoro–Shapiro integral (with $d^2z=2\,dx\,dy$). Then
--
--   $$
--   C(a,b)=\frac{2\pi\,\Gamma(c)}{\Gamma(1-a)\,\Gamma(1-b)}\int_0^1 d\beta\;(1-\beta)^{a-1}\beta^{b-1}.
--   $$
--
--   This is the last intermediate form in Tong's computation: the remaining integral is an Euler Beta integral (6.27), which yields eq. (6.11).
--
--   **Formalization Note** The integral is over the open interval $(0,1)$, with principal-branch complex powers of positive reals.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Appendix 6.5, p. 158 ('We write c = 1 − a − b. Finally, we're left with ...')

import Mathlib
import Definitions.Def_TongString_vs_integral

namespace TongString

open Complex MeasureTheory

theorem vs_integral_beta_form (a b c : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re)
    (habc : a + b + c = 1) :
    virasoroShapiroIntegral a b =
      2 * Real.pi * Gamma c / (Gamma (1 - a) * Gamma (1 - b)) *
        ∫ β in Set.Ioo (0 : ℝ) 1, ((1 - β : ℝ) : ℂ) ^ (a - 1) * (β : ℂ) ^ (b - 1) := by sorry

end TongString
