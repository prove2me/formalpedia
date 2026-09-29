-- Prove2me | Theorems.Thm_Pendulum_exactPeriod_series
-- name    : Pendulum.exactPeriod_series
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T17:37:52.35819+00:00
-- url     : https://prove2.me/theorems/d3f5b86a-5974-429b-a7f2-ca159d2f0c66
-- title:
--   Legendre series: $T=2\pi\sqrt{\ell/g}\sum_n\left(\frac{(2n)!}{2^{2n}(n!)^2}\right)^2\sin^{2n}(\theta_0/2)$
-- statement:
--   The **Legendre polynomial solution for the elliptic integral** turns the closed form of the period
--   into a convergent power series in $\sin(\theta_0/2)$.
--
--   Let $g,\ell>0$ and $0\le\theta_0<\pi$. Then the exact period
--   $T=4\sqrt{\ell/g}\,K(\sin(\theta_0/2))$ of a simple pendulum of length $\ell$ released from rest at
--   amplitude $\theta_0$ satisfies
--
--   $$T=2\pi\sqrt{\frac{\ell}{g}}\;\sum_{n=0}^{\infty}
--   \left(\frac{(2n)!}{2^{2n}\,(n!)^{2}}\right)^{\!2}\sin^{2n}\!\frac{\theta_0}{2}.$$
--
--   The coefficient $(2n)!/(2^{2n}(n!)^2)$ is the classical $\frac{(2n-1)!!}{(2n)!!}$ of the Legendre
--   expansion. The term $n=0$ contributes the small-angle period $T_0=2\pi\sqrt{\ell/g}$ and the term
--   $n=1$ contributes $T_0\sin^2(\theta_0/2)/4$, so truncating gives the familiar correction
--   $T\approx T_0\left(1+\theta_0^2/16\right)$; Figure 4 of the article plots the relative error of
--   these truncations.
--
--   **Formalization Note** The amplitude $\theta_0=0$ is allowed, where the series reduces to its first
--   term; the series diverges as $\theta_0\to\pi$, which is why the amplitude is bounded away from the
--   vertical.
-- source:
--   Wikipedia, Pendulum (mechanics), revision 1374595895, https://en.wikipedia.org/w/index.php?title=Pendulum_(mechanics)&oldid=1374595895

import Mathlib
import Definitions.Def_PendulumDefs

namespace Pendulum

theorem exactPeriod_series (g l theta0 : ℝ) (hg : 0 < g) (hl : 0 < l)
    (hpos : 0 ≤ theta0) (hlt : theta0 < Real.pi) :
    exactPeriod g l theta0
      = 2 * Real.pi * Real.sqrt (l / g) *
        ∑' n : ℕ, (((2 * n).factorial : ℝ) / (2 ^ (2 * n) * (n.factorial : ℝ) ^ 2)) ^ 2
          * Real.sin (theta0 / 2) ^ (2 * n) := by sorry

end Pendulum
