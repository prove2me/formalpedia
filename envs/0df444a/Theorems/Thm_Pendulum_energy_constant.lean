-- Prove2me | Theorems.Thm_Pendulum_energy_constant
-- name    : Pendulum.energy_constant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T17:22:54.624284+00:00
-- url     : https://prove2.me/theorems/47db1a67-90e0-4e20-b5e8-d2d2921afb10
-- title:
--   Conservation of energy: $\tfrac12\omega^2-\tfrac{g}{\ell}\cos\theta$ is constant
-- statement:
--   Mechanical energy is conserved along every motion of the simple pendulum.
--
--   Let $g,\ell\in\mathbb R$ and let $(\theta,\omega,\alpha)$ be a motion of the pendulum, so that
--   $\theta'=\omega$, $\omega'=\alpha$ and $\alpha=-(g/\ell)\sin\theta$ everywhere. Define the energy
--   per unit of $m\ell^2$ by
--
--   $$E(t)=\frac{\omega(t)^2}{2}-\frac{g}{\ell}\cos\theta(t).$$
--
--   Then for every $t\in\mathbb R$,
--
--   $$E(t)=E(0).$$
--
--   The first term is the kinetic energy of the bob and the second its gravitational potential energy,
--   both divided by $m\ell^2$; the statement is the "energy" derivation of Eq. 1 of the article, read
--   in the direction that the later sections use. Its immediate consequence is the first integral of
--   motion (Eq. 2), and through that the quarter-period integral and the closed form of the period.
-- source:
--   Wikipedia, Pendulum (mechanics), revision 1374595895, https://en.wikipedia.org/w/index.php?title=Pendulum_(mechanics)&oldid=1374595895

import Mathlib
import Definitions.Def_PendulumDefs

namespace Pendulum

theorem energy_constant (g l : ℝ) (theta omega alpha : ℝ → ℝ)
    (h : IsMotion g l theta omega alpha) (t : ℝ) :
    energy g l theta omega t = energy g l theta omega 0 := by sorry

end Pendulum
