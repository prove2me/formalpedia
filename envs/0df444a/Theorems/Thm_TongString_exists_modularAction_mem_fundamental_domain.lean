-- Prove2me | Theorems.Thm_TongString_exists_modularAction_mem_fundamental_domain
-- name    : TongString.exists_modularAction_mem_fundamental_domain
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T20:58:27.657918+00:00
-- url     : https://prove2.me/theorems/92787276-ce6a-4ab6-80d4-4274a566cab3
-- title:
--   Every $\tau\in\mathbb H$ is equivalent to a point with $|\tau|\ge1$, $|\operatorname{Re}\tau|\le\frac12$
-- statement:
--   Let $\tau\in\mathbb C$ with $\operatorname{Im}\tau>0$. Then there are integers $a,b,c,d$ with $ad-bc=1$ such that $\tau'=\dfrac{a\tau+b}{c\tau+d}$ lies in the fundamental domain
--
--   $$
--   \mathcal F=\Bigl\{\tau' : |\tau'|\ge1,\ \ -\tfrac12\le\operatorname{Re}\tau'\le\tfrac12\Bigr\}.
--   $$
--
--   Hence the moduli space of tori is covered by $\mathcal F$, which is why the one-loop string amplitude is an integral over $\mathcal F$ only.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 6.4.1, p. 147 ('One can show that by successive combinations of S and T, it is possible to map any point to lie within the shaded region ...')

import Mathlib
import Definitions.Def_TongString_modular_action

namespace TongString

theorem exists_modularAction_mem_fundamental_domain (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧
      1 ≤ ‖modularAction a b c d τ‖ ∧ |(modularAction a b c d τ).re| ≤ 1 / 2 := by sorry

end TongString
