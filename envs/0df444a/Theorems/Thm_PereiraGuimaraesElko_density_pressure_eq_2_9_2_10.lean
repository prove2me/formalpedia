-- Prove2me | Theorems.Thm_PereiraGuimaraesElko_density_pressure_eq_2_9_2_10
-- name    : PereiraGuimaraesElko.density_pressure_eq_2_9_2_10
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:51:46.104708+00:00
-- url     : https://prove2.me/theorems/65d26bb2-2190-4f2d-8cce-ee5a17927c00
-- title:
--   Eqs. (2.9)–(2.10): (2.6)–(2.7) are the FRW equations for the Elko energy density and pressure
-- statement:
--   Let $\kappa,H,\dot H,\Phi,\dot\Phi,V$ be real numbers (instantaneous values) and define the energy density and pressure of the Elko field by
--   $$\rho=\frac{\dot\Phi^2}{2}+V+\frac38\,\frac{H^2\Phi^2}{1+\kappa^2\Phi^2/8},\qquad(2.9)$$
--   $$p=\frac{\dot\Phi^2}{2}-V-\frac38\,\frac{H^2\Phi^2}{1+\kappa^2\Phi^2/8}-\frac14\,\frac{\dot H\Phi^2}{1+\kappa^2\Phi^2/8}-\frac12\,\frac{H\Phi\dot\Phi}{(1+\kappa^2\Phi^2/8)^2}.\qquad(2.10)$$
--   Then:
--
--   1. equation (2.6) holds if and only if $H^2=\dfrac{\kappa^2}{3}\rho$;
--   2. equation (2.7) holds if and only if $\dot H=-\dfrac{\kappa^2}{2}(\rho+p)$.
--
--   So $\rho$ and $p$ are exactly the quantities that make the Elko system look like a perfect fluid in the standard Friedmann equations; the equation-of-state parameter $\omega=p/\rho$ of Section 3.2 is built from them.
--
--   **Formalization Note** The source lists (2.9)–(2.10) alongside (2.6)–(2.8) and identifies them, in Appendix A, as the energy density and pressure; this item records the precise sense in which that is true.
-- source:
--   S. H. Pereira and T. M. Guimarães, "From inflation to recent cosmic acceleration: the fermionic Elko field driving the evolution of the universe", JCAP 09 (2017) 038, https://doi.org/10.1088/1475-7516/2017/09/038 (arXiv:1702.07385), p. 5, Eqs. (2.6), (2.7), (2.9), (2.10); p. 14, remark after (A.17) that the right sides of (A.14), (A.15) are energy density and pressure

import Mathlib

namespace PereiraGuimaraesElko

theorem density_pressure_eq_2_9_2_10 (κ H Hdot Φ Φdot V ρ p : ℝ)
    (h29 : ρ = Φdot ^ 2 / 2 + V + 3 / 8 * (H ^ 2 * Φ ^ 2) / (1 + κ ^ 2 * Φ ^ 2 / 8))
    (h210 : p = Φdot ^ 2 / 2 - V - 3 / 8 * (H ^ 2 * Φ ^ 2) / (1 + κ ^ 2 * Φ ^ 2 / 8)
        - 1 / 4 * (Hdot * Φ ^ 2) / (1 + κ ^ 2 * Φ ^ 2 / 8)
        - 1 / 2 * (H * Φ * Φdot) / (1 + κ ^ 2 * Φ ^ 2 / 8) ^ 2) :
    (H ^ 2 = κ ^ 2 / 3 * (1 + κ ^ 2 * Φ ^ 2 / 8) * (Φdot ^ 2 / 2 + V) ↔
        H ^ 2 = κ ^ 2 / 3 * ρ) ∧
      (Hdot = -(κ ^ 2 / 2) * (1 + κ ^ 2 * Φ ^ 2 / 8) *
          (Φdot ^ 2 - 1 / 2 * (H * Φ * Φdot) / (1 + κ ^ 2 * Φ ^ 2 / 8) ^ 2) ↔
        Hdot = -(κ ^ 2 / 2) * (ρ + p)) := by
  sorry

end PereiraGuimaraesElko
