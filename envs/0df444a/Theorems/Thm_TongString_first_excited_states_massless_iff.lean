-- Prove2me | Theorems.Thm_TongString_first_excited_states_massless_iff
-- name    : TongString.first_excited_states_massless_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T20:53:26.470601+00:00
-- url     : https://prove2.me/theorems/b85a6c1c-17c7-482f-88ec-41f2a8e167bf
-- title:
--   First excited states are massless iff $D=26$
-- statement:
--   Let $\alpha'>0$ and let $D$ be a natural number. The first excited states $\tilde\alpha^i_{-1}\alpha^j_{-1}|0;p\rangle$ of the closed string have, by the mass formula (2.26) at level $N=\tilde N=1$,
--
--   $$
--   M^2=\frac{4}{\alpha'}\left(1-\frac{D-2}{24}\right),
--   $$
--
--   and this vanishes if and only if $D=26$. This is Tong's first derivation of the critical dimension: Lorentz invariance requires these $(D-2)^2$ states to be massless.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 2.3.2, pp. 41–42 (mass of the states (2.28) from (2.26); 'this is only the case if the dimension of spacetime is D = 26')

import Mathlib

namespace TongString

theorem first_excited_states_massless_iff (α' : ℝ) (hα' : 0 < α') (D : ℕ) :
    4 / α' * (1 - ((D : ℝ) - 2) / 24) = 0 ↔ D = 26 := by sorry

end TongString
