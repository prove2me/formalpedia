-- Prove2me | Theorems.Thm_PereiraGuimaraesElko_friedmann_eq_2_6
-- name    : PereiraGuimaraesElko.friedmann_eq_2_6
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:49:50.882616+00:00
-- url     : https://prove2.me/theorems/0c156fbd-bb98-48fe-82bd-95973af17e5b
-- title:
--   Eq. (2.6): eliminating the torsion from the first Friedmann equation (2.2)
-- statement:
--   Let $\kappa,H,h,\Phi,\dot\Phi,V$ be real numbers (the values at one instant of the Hubble rate, the torsion function, the Elko field, its velocity and the potential $V(\Phi)$). Assume the torsion relation (2.5),
--   $$h=-\frac18\,\frac{\kappa^2\Phi^2}{1+\kappa^2\Phi^2/8}\,H.$$
--   Then the first Friedmann equation (2.2),
--   $$H^2=\frac{\kappa^2}{3}\left[\frac{\dot\Phi^2}{2}+V+\frac38H^2\Phi^2+\frac34Hh\Phi^2\right]+\left(1+\frac{\kappa^2\Phi^2}{8}\right)h^2,$$
--   holds if and only if
--   $$H^2=\frac{\kappa^2}{3}\left(1+\frac{\kappa^2\Phi^2}{8}\right)\left[\frac{\dot\Phi^2}{2}+V\right].\qquad(2.6)$$
--
--   Equation (2.6) shows that, once the torsion is eliminated, the Elko Friedmann equation is the standard scalar-field one multiplied by the factor $1+\kappa^2\Phi^2/8$.
--
--   **Formalization Note** The equation is pointwise in time, so it is stated for real numbers. The source states the direction (2.2) $\Rightarrow$ (2.6); the converse also holds and is included.
-- source:
--   S. H. Pereira and T. M. Guimarães, "From inflation to recent cosmic acceleration: the fermionic Elko field driving the evolution of the universe", JCAP 09 (2017) 038, https://doi.org/10.1088/1475-7516/2017/09/038 (arXiv:1702.07385), p. 5, Eqs. (2.2), (2.5), (2.6)

import Mathlib

namespace PereiraGuimaraesElko

theorem friedmann_eq_2_6 (κ H h Φ Φdot V : ℝ)
    (h25 : h = -(1 / 8) * (κ ^ 2 * Φ ^ 2 / (1 + κ ^ 2 * Φ ^ 2 / 8)) * H) :
    H ^ 2 = κ ^ 2 / 3 * (Φdot ^ 2 / 2 + V + 3 / 8 * H ^ 2 * Φ ^ 2 + 3 / 4 * H * h * Φ ^ 2)
        + (1 + κ ^ 2 * Φ ^ 2 / 8) * h ^ 2 ↔
      H ^ 2 = κ ^ 2 / 3 * (1 + κ ^ 2 * Φ ^ 2 / 8) * (Φdot ^ 2 / 2 + V) := by sorry

end PereiraGuimaraesElko
