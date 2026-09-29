-- Prove2me | Theorems.Thm_Pendulum_sq_angularVelocity_eq
-- name    : Pendulum.sq_angularVelocity_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T17:24:27.357486+00:00
-- url     : https://prove2.me/theorems/ffb6af9a-1042-43b7-8ec7-86304a94ecb3
-- title:
--   Eq. 2: $(d\theta/dt)^2=\tfrac{2g}{\ell}(\cos\theta-\cos\theta_0)$
-- statement:
--   This is **Eq. 2** of the article, the first integral of motion.
--
--   Let $g,\ell\in\mathbb R$, let $(\theta,\omega,\alpha)$ be a motion of the pendulum, and suppose the
--   pendulum is released from rest at the angle $\theta_0$:
--
--   $$\theta(0)=\theta_0,\qquad \omega(0)=0 .$$
--
--   Then at every time $t$,
--
--   $$\omega(t)^2=\frac{2g}{\ell}\bigl(\cos\theta(t)-\cos\theta_0\bigr).$$
--
--   The identity expresses the angular velocity in terms of the angle alone, the integration constant
--   being fixed by the initial displacement $\theta_0$; differentiating it returns Eq. 1. In the
--   article it is the starting point of the computation of the period for an arbitrary amplitude: one
--   inverts it to express $dt$ in terms of $d\theta$ and integrates over a quarter cycle.
--
--   **Formalization Note** The statement is the squared form, so it carries no choice of sign for
--   $\omega$; the sign is recovered from the direction of travel where it is needed.
-- source:
--   Wikipedia, Pendulum (mechanics), revision 1374595895, https://en.wikipedia.org/w/index.php?title=Pendulum_(mechanics)&oldid=1374595895

import Mathlib
import Definitions.Def_PendulumDefs

namespace Pendulum

theorem sq_angularVelocity_eq (g l theta0 : ℝ) (theta omega alpha : ℝ → ℝ)
    (h : IsMotion g l theta omega alpha) (hinit : theta 0 = theta0) (hrest : omega 0 = 0)
    (t : ℝ) :
    omega t ^ 2 = 2 * (g / l) * (Real.cos (theta t) - Real.cos theta0) := by sorry

end Pendulum
