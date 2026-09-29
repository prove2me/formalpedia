-- Prove2me | Theorems.Thm_Pendulum_harmonic_solution
-- name    : Pendulum.harmonic_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T17:36:11.44199+00:00
-- url     : https://prove2.me/theorems/751fbe40-baa7-4f28-9135-dd306cb6df5a
-- title:
--   Small-angle approximation: $\theta(t)=\theta_0\cos(wt)$
-- statement:
--   The **small-angle approximation** of the article replaces $\sin\theta$ by $\theta$ in Eq. 1 and so
--   replaces the pendulum by a harmonic oscillator. This is the solution of that linear equation.
--
--   Let $w,\theta_0\in\mathbb R$ and let $(\theta,\omega,\alpha)$ be a harmonic motion of angular
--   frequency $w$, that is $\theta'=\omega$, $\omega'=\alpha$ and
--
--   $$\alpha(t)=-w^2\,\theta(t)\qquad(t\in\mathbb R).$$
--
--   If the motion starts at rest from $\theta_0$, i.e. $\theta(0)=\theta_0$ and $\omega(0)=0$, then
--
--   $$\theta(t)=\theta_0\cos(wt)\qquad\text{for all }t\in\mathbb R .$$
--
--   The motion is simple harmonic with amplitude $\theta_0$, the maximum angle between the rod and the
--   vertical. For the pendulum one takes $w=\sqrt{g/\ell}$; for the compound pendulum, $w=\sqrt{mgr/I_O}$.
--
--   **Formalization Note** The degenerate case $w=0$ is included and gives the constant motion
--   $\theta\equiv\theta_0$.
-- source:
--   Wikipedia, Pendulum (mechanics), revision 1374595895, https://en.wikipedia.org/w/index.php?title=Pendulum_(mechanics)&oldid=1374595895

import Mathlib
import Definitions.Def_PendulumDefs

namespace Pendulum

theorem harmonic_solution (w theta0 : ℝ) (theta omega alpha : ℝ → ℝ)
    (h : IsHarmonicMotion w theta omega alpha) (hinit : theta 0 = theta0) (hrest : omega 0 = 0) :
    ∀ t, theta t = theta0 * Real.cos (w * t) := by sorry

end Pendulum
