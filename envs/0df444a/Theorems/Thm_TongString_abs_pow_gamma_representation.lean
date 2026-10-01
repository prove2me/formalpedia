-- Prove2me | Theorems.Thm_TongString_abs_pow_gamma_representation
-- name    : TongString.abs_pow_gamma_representation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T20:52:16.954074+00:00
-- url     : https://prove2.me/theorems/5a7fe579-c1f1-4e45-b5f8-4d6a347905fa
-- title:
--   $|z|^{2a-2}=\frac{1}{\Gamma(1-a)}\int_0^\infty t^{-a}e^{-|z|^2t}\,dt$
-- statement:
--   Let $r>0$ be a real number and let $a\in\mathbb C$ with $\operatorname{Re}a<1$. Then
--
--   $$
--   r^{2a-2}=\frac{1}{\Gamma(1-a)}\int_0^\infty dt\; t^{-a}\,e^{-r^2 t}.
--   $$
--
--   Applied with $r=|z|$ (and, with $b$ in place of $a$, with $r=|1-z|$) this is the "trick" with which Tong rewrites both factors of the Virasoro–Shapiro integrand as Gamma-type integrals; it follows from the integral definition (6.26) of $\Gamma$.
--
--   **Formalization Note** Powers are principal-branch complex powers of positive reals; the integral is over the open half-line $(0,\infty)$ with Lebesgue measure.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Appendix 6.5, p. 157 (last display) – p. 158 (first display), consequence of eq. (6.26)

import Mathlib

namespace TongString

open Complex MeasureTheory

theorem abs_pow_gamma_representation (r : ℝ) (hr : 0 < r) (a : ℂ) (ha : a.re < 1) :
    (r : ℂ) ^ (2 * a - 2) =
      1 / Gamma (1 - a) *
        ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-a) * Complex.exp (-((r : ℂ) ^ 2 * t)) := by sorry

end TongString
