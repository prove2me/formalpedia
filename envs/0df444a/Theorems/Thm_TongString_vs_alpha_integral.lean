-- Prove2me | Theorems.Thm_TongString_vs_alpha_integral
-- name    : TongString.vs_alpha_integral
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T20:55:45.694659+00:00
-- url     : https://prove2.me/theorems/51ec8c82-c0fd-45e8-ba07-034d5c31f245
-- title:
--   $\int_0^\infty d\alpha\,\alpha^{-a-b}e^{-\beta\alpha(1-\beta)}=[\beta(1-\beta)]^{a+b-1}\Gamma(1-a-b)$
-- statement:
--   Let $a,b\in\mathbb C$ with $\operatorname{Re}(a+b)<1$ and let $\beta\in(0,1)$. Then
--
--   $$
--   \int_0^\infty d\alpha\;\alpha^{-a-b}\,e^{-\beta\alpha(1-\beta)}=[\beta(1-\beta)]^{a+b-1}\,\Gamma(1-a-b).
--   $$
--
--   This is the $\alpha$-integral that Tong "recognizes" in the Virasoro–Shapiro computation: a rescaled Gamma integral with scale $\beta(1-\beta)>0$.
--
--   **Formalization Note** Powers are principal-branch complex powers of positive reals; the integral is over the open half-line $(0,\infty)$.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Appendix 6.5, p. 158 ('But we recognize the integral over dα: it is simply ...')

import Mathlib

namespace TongString

open Complex MeasureTheory

theorem vs_alpha_integral (a b : ℂ) (hab : (a + b).re < 1) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ α in Set.Ioi (0 : ℝ),
        (α : ℂ) ^ (-a - b) * Complex.exp (-((β * (1 - β) : ℝ) : ℂ) * α)) =
      ((β * (1 - β) : ℝ) : ℂ) ^ (a + b - 1) * Gamma (1 - a - b) := by sorry

end TongString
