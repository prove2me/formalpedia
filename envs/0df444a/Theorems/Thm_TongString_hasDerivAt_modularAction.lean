-- Prove2me | Theorems.Thm_TongString_hasDerivAt_modularAction
-- name    : TongString.hasDerivAt_modularAction
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T21:01:45.811731+00:00
-- url     : https://prove2.me/theorems/c641fb4c-7283-4938-a78f-7ba8e20ff93c
-- title:
--   $\frac{d}{d\tau}\frac{a\tau+b}{c\tau+d}=\frac{1}{(c\tau+d)^2}$, so $d^2\tau\to d^2\tau/|c\tau+d|^4$
-- statement:
--   Let $a,b,c,d\in\mathbb Z$ with $ad-bc=1$ and let $\tau\in\mathbb C$ with $\operatorname{Im}\tau>0$. Then the map $\tau\mapsto\dfrac{a\tau+b}{c\tau+d}$ is complex differentiable at $\tau$ with
--
--   $$
--   \frac{d}{d\tau}\,\frac{a\tau+b}{c\tau+d}=\frac{1}{(c\tau+d)^{2}}.
--   $$
--
--   Since the real Jacobian of a holomorphic map is $|f'(\tau)|^2$, this gives Tong's rule $d^2\tau\to d^2\tau/|c\tau+d|^4$.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 6.4.1, p. 147 (transformation of d²τ under (6.19))

import Mathlib
import Definitions.Def_TongString_modular_action

namespace TongString

theorem hasDerivAt_modularAction (a b c d : ℤ) (h : a * d - b * c = 1) (τ : ℂ) (hτ : 0 < τ.im) :
    HasDerivAt (modularAction a b c d) (1 / (c * τ + d) ^ 2) τ := by sorry

end TongString
