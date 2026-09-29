-- Prove2me | Theorems.Thm_Pendulum_quarterPeriod_eq_ellipticK
-- name    : Pendulum.quarterPeriod_eq_ellipticK
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T17:37:26.542985+00:00
-- url     : https://prove2.me/theorems/90a3952a-6487-4071-ae8e-d6b4fde778f4
-- title:
--   Eq. 3: $\int_0^{\theta_0}\frac{d\theta}{\sqrt{\cos\theta-\cos\theta_0}}=\sqrt2\,K(\sin(\theta_0/2))$
-- statement:
--   This is the analytic heart of the article's **arbitrary-amplitude period** computation, its Eq. 3.
--
--   Let $0<\theta_0<\pi$. Then
--
--   $$\int_{0}^{\theta_0}\frac{d\theta}{\sqrt{\cos\theta-\cos\theta_0}}
--   =\sqrt2\;K\!\left(\sin\frac{\theta_0}{2}\right),
--   \qquad
--   K(k)=\int_0^{\pi/2}\frac{du}{\sqrt{1-k^2\sin^2u}} .$$
--
--   Inverting Eq. 2 and integrating over a quarter cycle expresses the quarter period of the pendulum
--   as the integral on the left, multiplied by $\sqrt{\ell/(2g)}$; the identity above converts it into
--   the complete elliptic integral of the first kind, which is how the closed form
--   $T=4\sqrt{\ell/g}\,K(\sin(\theta_0/2))$ arises.
--
--   The integral on the left is improper: the integrand blows up like $(\theta_0-\theta)^{-1/2}$ at the
--   upper endpoint. The singularity is integrable precisely because $\theta_0<\pi$; as the article
--   notes, at $\theta_0=\pi$ it ceases to be integrable, which is the analytic form of the statement
--   that a pendulum with exactly enough energy to reach the vertical takes infinitely long to get
--   there.
--
--   **Formalization Note** The left-hand side is an interval integral of a function that is defined,
--   but unbounded, on the open interval; part of the content of the statement is that this integral
--   converges to the stated value.
-- source:
--   Wikipedia, Pendulum (mechanics), revision 1374595895, https://en.wikipedia.org/w/index.php?title=Pendulum_(mechanics)&oldid=1374595895

import Mathlib
import Definitions.Def_PendulumDefs

namespace Pendulum

theorem quarterPeriod_eq_ellipticK (theta0 : ℝ) (hpos : 0 < theta0) (hlt : theta0 < Real.pi) :
    (∫ x in (0 : ℝ)..theta0, (Real.sqrt (Real.cos x - Real.cos theta0))⁻¹)
      = Real.sqrt 2 * ellipticK (Real.sin (theta0 / 2)) := by sorry

end Pendulum
