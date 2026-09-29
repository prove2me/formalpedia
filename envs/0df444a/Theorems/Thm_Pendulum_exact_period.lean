-- Prove2me | Theorems.Thm_Pendulum_exact_period
-- name    : Pendulum.exact_period
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-19T17:47:06.877979+00:00
-- url     : https://prove2.me/theorems/d1729435-af17-47aa-b612-778b864ff289
-- title:
--   The exact period of the simple gravity pendulum is $4\sqrt{\ell/g}\,K(\sin(\theta_0/2))$
-- statement:
--   **The goal of the mission.** For a simple gravity pendulum of finite amplitude the period is given
--   in closed form by a complete elliptic integral of the first kind, and it is the *exact* period: no
--   smaller positive number is a period of the motion.
--
--   Let $g>0$ be the gravitational field, $\ell>0$ the length of the rod and $0<\theta_0<\pi$ the
--   amplitude, and let $(\theta,\omega,\alpha)$ be a motion of the pendulum released from rest at
--   $\theta_0$, i.e. satisfying Eq. 1,
--
--   $$\frac{d^2\theta}{dt^2}=-\frac{g}{\ell}\sin\theta,
--   \qquad \theta(0)=\theta_0,\qquad \frac{d\theta}{dt}(0)=0 .$$
--
--   Put
--
--   $$T=4\sqrt{\frac{\ell}{g}}\;K\!\left(\sin\frac{\theta_0}{2}\right),
--   \qquad K(k)=\int_0^{\pi/2}\frac{du}{\sqrt{1-k^2\sin^2u}} .$$
--
--   Then
--
--   1. $\theta(t+T)=\theta(t)$ for every $t\in\mathbb R$; and
--   2. no $S$ with $0<S<T$ satisfies $\theta(t+S)=\theta(t)$ for every $t\in\mathbb R$.
--
--   So $T$ is the minimal period of the oscillation. This is Eq. 3 of the article, upgraded from a
--   formula for "the period" to a statement about the solution of the differential equation itself. It
--   contains Huygens's law as a limit: as $\theta_0\to0$, $K(\sin(\theta_0/2))\to\pi/2$ and $T\to
--   T_0=2\pi\sqrt{\ell/g}$, while for $\theta_0=10^\circ$, $\ell=1\,\mathrm m$ and
--   $g=9.80665\,\mathrm{m/s^2}$ one gets $T\approx2.0102\,\mathrm s$ against $T_0\approx2.0064\,\mathrm
--   s$, a difference of less than $0.2\%$ — the numbers quoted in the article.
--
--   **Formalization Note** The amplitude is restricted to $0<\theta_0<\pi$: at $\theta_0=0$ the
--   pendulum is at rest and every number is a period, and at $\theta_0=\pi$ the motion is the upright
--   equilibrium and $K$ diverges. Existence of a motion with the given initial data is a separate
--   milestone, so the statement is not vacuous.
-- source:
--   Wikipedia, Pendulum (mechanics), revision 1374595895, https://en.wikipedia.org/w/index.php?title=Pendulum_(mechanics)&oldid=1374595895

import Mathlib
import Definitions.Def_PendulumDefs

namespace Pendulum

theorem exact_period (g l theta0 : ℝ) (hg : 0 < g) (hl : 0 < l)
    (hpos : 0 < theta0) (hlt : theta0 < Real.pi)
    (theta omega alpha : ℝ → ℝ) (h : IsMotion g l theta omega alpha)
    (hinit : theta 0 = theta0) (hrest : omega 0 = 0) :
    Function.Periodic theta (exactPeriod g l theta0) ∧
      ∀ T, 0 < T → T < exactPeriod g l theta0 → ¬ Function.Periodic theta T := by sorry

end Pendulum
