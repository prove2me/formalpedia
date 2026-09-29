-- Prove2me | Theorems.Thm_Pendulum_smallAngle_period
-- name    : Pendulum.smallAngle_period
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T17:36:37.370086+00:00
-- url     : https://prove2.me/theorems/0f135d1f-06ef-4ce3-9574-eeff573039fe
-- title:
--   Huygens's law: the small-angle period is $T_0=2\pi\sqrt{\ell/g}$, independent of amplitude
-- statement:
--   **Huygens's law for the period.** In the small-angle regime the pendulum is a harmonic oscillator
--   of angular frequency $\sqrt{g/\ell}$, and its period does not depend on the amplitude.
--
--   Let $g,\ell>0$ and $\theta_0\in\mathbb R$, and let $(\theta,\omega,\alpha)$ be a harmonic motion of
--   angular frequency $w=\sqrt{g/\ell}$ released from rest at $\theta_0$, i.e. $\theta'=\omega$,
--   $\omega'=\alpha$, $\alpha=-\frac{g}{\ell}\theta$, $\theta(0)=\theta_0$ and $\omega(0)=0$. Then
--
--   $$\theta(t)=\theta_0\cos\!\left(\sqrt{\tfrac{g}{\ell}}\;t\right)\qquad(t\in\mathbb R),$$
--
--   and $\theta$ is periodic with period
--
--   $$T_0=2\pi\sqrt{\frac{\ell}{g}} .$$
--
--   The period $T_0$ involves only the length and the gravitational field: it is independent of the
--   amplitude $\theta_0$. This is the **isochronism** that Galileo observed and that makes the
--   pendulum usable as a clock; the mission's goal theorem quantifies its failure for the true,
--   nonlinear equation.
-- source:
--   Wikipedia, Pendulum (mechanics), revision 1374595895, https://en.wikipedia.org/w/index.php?title=Pendulum_(mechanics)&oldid=1374595895

import Mathlib
import Definitions.Def_PendulumDefs

namespace Pendulum

theorem smallAngle_period (g l theta0 : ℝ) (hg : 0 < g) (hl : 0 < l)
    (theta omega alpha : ℝ → ℝ)
    (h : IsHarmonicMotion (Real.sqrt (g / l)) theta omega alpha)
    (hinit : theta 0 = theta0) (hrest : omega 0 = 0) :
    (∀ t, theta t = theta0 * Real.cos (Real.sqrt (g / l) * t)) ∧
      Function.Periodic theta (smallAnglePeriod g l) := by sorry

end Pendulum
