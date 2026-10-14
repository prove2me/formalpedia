-- Prove2me | Theorems.Thm_PereiraGuimaraesElko_appendix_A_gives_eqs_2_2_to_2_4
-- name    : PereiraGuimaraesElko.appendix_A_gives_eqs_2_2_to_2_4
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:49:24.160998+00:00
-- url     : https://prove2.me/theorems/e938f641-fb53-43bf-8c67-c96ca28c0f79
-- title:
--   Appendix A: Eqs. (A.14)–(A.16) with $f=0$ give the torsion-coupled Friedmann equations (2.2)–(2.4)
-- statement:
--   Let $\kappa\in\mathbb R$, let $H,h,f,\Phi,V$ be real functions and fix a time $t$. Suppose that at $t$ the Euler–Lagrange equations (A.14), (A.15), (A.16) hold (in the form stated in the milestone for Eqs. (A.14)–(A.17), with $\dot H$, $\ddot\Phi$ and $\frac{d}{dt}[(H+h)\Phi^2]$ the derivatives at $t$), and that the second torsion function vanishes, $f(t)=0$. Then at $t$:
--   $$
--   H^2=\frac{\kappa^2}{3}\left[\frac{\dot\Phi^2}{2}+V(\Phi)+\frac38H^2\Phi^2+\frac34Hh\Phi^2\right]+\left(1+\frac{\kappa^2\Phi^2}{8}\right)h^2,\qquad(2.2)
--   $$
--   $$
--   \dot H=-\frac{\kappa^2}{2}\left[\dot\Phi^2+\frac34Hh\Phi^2-\frac14\frac{d}{dt}\big[(H+h)\Phi^2\big]\right]-3\left(1+\frac{\kappa^2\Phi^2}{8}\right)h^2,\qquad(2.3)
--   $$
--   $$
--   \ddot\Phi+3H\dot\Phi+V'(\Phi)-\frac34(H+h)^2\Phi=0.\qquad(2.4)
--   $$
--
--   This is the step that turns the variational field equations of Appendix A into the Friedmann system used in Section 2.
--
--   **Formalization Note** Only $f=0$ from (A.17) is needed for this step; the formula for $h$ is not used, so it is not assumed.
-- source:
--   S. H. Pereira and T. M. Guimarães, "From inflation to recent cosmic acceleration: the fermionic Elko field driving the evolution of the universe", JCAP 09 (2017) 038, https://doi.org/10.1088/1475-7516/2017/09/038 (arXiv:1702.07385), p. 14, Appendix A, last paragraph (substituting (A.17) into (A.14)–(A.16)); target equations (2.2)–(2.4) on p. 5

import Mathlib

namespace PereiraGuimaraesElko

theorem appendix_A_gives_eqs_2_2_to_2_4 (κ : ℝ) (H h f Φ V : ℝ → ℝ) (t : ℝ)
    (hA14 : 3 * H t ^ 2 = κ ^ 2 * (deriv Φ t ^ 2 / 2 + V (Φ t) + 3 / 8 * H t ^ 2 * Φ t ^ 2
          + 3 / 4 * H t * h t * Φ t ^ 2)
        + 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * h t ^ 2
        + 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * f t ^ 2)
    (hA15 : -2 * deriv H t - 3 * H t ^ 2 = κ ^ 2 * (deriv Φ t ^ 2 / 2 - V (Φ t)
          - 3 / 8 * H t ^ 2 * Φ t ^ 2 - 1 / 4 * deriv (fun s => (H s + h s) * Φ s ^ 2) t)
        + 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * h t ^ 2
        - 3 * (1 + 1 / 8 * κ ^ 2 * Φ t ^ 2) * f t ^ 2)
    (hA16 : deriv (deriv Φ) t + 3 * H t * deriv Φ t + deriv V (Φ t)
        - 3 / 4 * ((H t + h t) ^ 2 - f t ^ 2) * Φ t = 0)
    (hf : f t = 0) :
    H t ^ 2 = κ ^ 2 / 3 * (deriv Φ t ^ 2 / 2 + V (Φ t)
        + 3 / 8 * H t ^ 2 * Φ t ^ 2 + 3 / 4 * H t * h t * Φ t ^ 2)
        + (1 + κ ^ 2 * Φ t ^ 2 / 8) * h t ^ 2 ∧
    deriv H t = -(κ ^ 2 / 2) * (deriv Φ t ^ 2 + 3 / 4 * H t * h t * Φ t ^ 2
        - 1 / 4 * deriv (fun s => (H s + h s) * Φ s ^ 2) t)
        - 3 * (1 + κ ^ 2 * Φ t ^ 2 / 8) * h t ^ 2 ∧
    deriv (deriv Φ) t + 3 * H t * deriv Φ t + deriv V (Φ t)
        - 3 / 4 * (H t + h t) ^ 2 * Φ t = 0 := by
  sorry

end PereiraGuimaraesElko
