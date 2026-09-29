-- Prove2me | Theorems.Thm_Pendulum_compound_period
-- name    : Pendulum.compound_period
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T17:38:11.555491+00:00
-- url     : https://prove2.me/theorems/4c224a65-9a48-4000-ad29-feadd6ac85ab
-- title:
--   Compound pendulum: period $2\pi\sqrt{I_O/(mgr)}$
-- statement:
--   The **compound (physical) pendulum**: an arbitrarily shaped rigid body swinging about a pivot.
--
--   Let $m>0$ be the total mass of the body, $r>0$ the distance from the pivot $O$ to its centre of
--   mass, $I_O>0$ its moment of inertia about the pivot, and $g>0$ the gravitational field. Under the
--   small-angle approximation the torque equation reads
--
--   $$I_O\,\frac{d^2\theta}{dt^2}=-m g r\,\theta,$$
--
--   a harmonic oscillator of angular frequency $w=\sqrt{mgr/I_O}$. If such a motion is released from
--   rest at an amplitude $\theta_0$, then $\theta$ is periodic with period
--
--   $$T=2\pi\sqrt{\frac{I_O}{m g r}} .$$
--
--   For a point mass at distance $\ell$ from the pivot one has $I_O=m\ell^2$ and $r=\ell$, and the
--   formula reduces to Huygens's law $T=2\pi\sqrt{\ell/g}$; in general the pendulum swings like a
--   simple pendulum of the **equivalent length** $\ell_{\mathrm{eq}}=I_O/(mr)$, for example
--   $\ell_{\mathrm{eq}}=\tfrac23\ell$ for a homogeneous rod of length $\ell$ swinging about its end.
-- source:
--   Wikipedia, Pendulum (mechanics), revision 1374595895, https://en.wikipedia.org/w/index.php?title=Pendulum_(mechanics)&oldid=1374595895

import Mathlib
import Definitions.Def_PendulumDefs

namespace Pendulum

theorem compound_period (m g r IO theta0 : ℝ) (hm : 0 < m) (hg : 0 < g) (hr : 0 < r)
    (hIO : 0 < IO) (theta omega alpha : ℝ → ℝ)
    (h : IsHarmonicMotion (Real.sqrt (m * g * r / IO)) theta omega alpha)
    (hinit : theta 0 = theta0) (hrest : omega 0 = 0) :
    Function.Periodic theta (2 * Real.pi * Real.sqrt (IO / (m * g * r))) := by sorry

end Pendulum
