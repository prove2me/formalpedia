-- Prove2me | Theorems.Thm_PiIrrationality_remainder_separation
-- name    : PiIrrationality.remainder_separation
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-03T06:18:09.322381+00:00
-- url     : https://prove2.me/theorems/6de20abc-f3bd-4820-bf0b-effa3560fd92
-- title:
--   Complex remainder separation with quantitative bounds
-- statement:
--   Let $z,y,R,U,T$ be complex numbers and let $a,t$ be positive real numbers. Suppose
--
--   $$R-U=(z-y)T,\qquad a\le |U|,\qquad |R|\le a/2,\qquad |T|<t.$$
--
--   Then
--
--   $$\frac{a}{2t}<|z-y|.$$
--
--   This quantitative form of the remainder-separation step applies to Hermite approximations to logarithms, including Mignotte’s construction at $z=i\pi/2$. The strict coefficient bound yields a strict approximation lower bound.
-- source:
--   M. Mignotte, Approximations rationnelles de π et quelques autres nombres, Mém. Soc. Math. France 37 (1974), pp. 123–125, Section II equations (9)–(16). https://www.numdam.org/item/MSMF_1974__37__121_0.pdf (doi:10.24033/msmf.139). General quantitative form of equations (9)–(10), with the lower bound on U and upper bound on T stated explicitly.

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem PiIrrationality.remainder_separation (z y R U T : ℂ) (a t : ℝ)
    (hidentity : R - U = (z - y) * T)
    (ha : 0 < a) (ht : 0 < t)
    (hU : a ≤ ‖U‖) (hR : ‖R‖ ≤ a / 2) (hT : ‖T‖ < t) :
    a / (2 * t) < ‖z - y‖ := by sorry
