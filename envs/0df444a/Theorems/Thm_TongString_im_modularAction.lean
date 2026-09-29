-- Prove2me | Theorems.Thm_TongString_im_modularAction
-- name    : TongString.im_modularAction
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T20:58:52.723903+00:00
-- url     : https://prove2.me/theorems/cbf61606-dc0d-4734-bf2f-c1e696d50834
-- title:
--   $\operatorname{Im}\tau\to\operatorname{Im}\tau/|c\tau+d|^2$ under a modular transformation
-- statement:
--   Let $a,b,c,d\in\mathbb Z$ with $ad-bc=1$ and let $\tau\in\mathbb C$ with $\operatorname{Im}\tau>0$. Then
--
--   $$
--   \operatorname{Im}\frac{a\tau+b}{c\tau+d}=\frac{\operatorname{Im}\tau}{|c\tau+d|^{2}}.
--   $$
--
--   This is one half of Tong's verification that the measure $d^2\tau/(\operatorname{Im}\tau)^2$ is modular invariant; in particular modular transformations preserve the upper half-plane.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 6.4.1, p. 147 (transformation of Im τ under (6.19))

import Mathlib
import Definitions.Def_TongString_modular_action

namespace TongString

theorem im_modularAction (a b c d : ℤ) (h : a * d - b * c = 1) (τ : ℂ) (hτ : 0 < τ.im) :
    (modularAction a b c d τ).im = τ.im / Complex.normSq (c * τ + d) := by sorry

end TongString
