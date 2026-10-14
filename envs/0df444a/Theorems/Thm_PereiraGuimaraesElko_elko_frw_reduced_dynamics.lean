-- Prove2me | Theorems.Thm_PereiraGuimaraesElko_elko_frw_reduced_dynamics
-- name    : PereiraGuimaraesElko.elko_frw_reduced_dynamics
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:52:56.100969+00:00
-- url     : https://prove2.me/theorems/fd9def83-e7eb-4063-bbcc-2d1ea8a30a0e
-- title:
--   Pereira–Guimarães 2017: the torsion-coupled Elko FRW system reduces to Eqs. (2.6)–(2.10)
-- statement:
--   Let $\kappa\in\mathbb R$ (with $\kappa^2=8\pi G$), let $I\subseteq\mathbb R$ be an open set of times, and let $H$ (Hubble rate), $h$ (torsion function), $\Phi$ (Elko field), $V$ (potential), $\rho$ and $p$ be real functions. Assume that $H$, $\Phi$ and $\dot\Phi$ are differentiable on $I$, that $V$ is differentiable, and that for every $t\in I$:
--
--   1. $h=-\dfrac18\dfrac{\kappa^2\Phi^2}{1+\kappa^2\Phi^2/8}H$ (2.5);
--   2. the first Friedmann equation with torsion (2.2) holds;
--   3. the second Friedmann equation with torsion (2.3) holds;
--   4. $\rho$ and $p$ are given by (2.9) and (2.10).
--
--   Then for every $t\in I$:
--   $$H^2=\frac{\kappa^2}{3}\left(1+\frac{\kappa^2\Phi^2}{8}\right)\left[\frac{\dot\Phi^2}{2}+V(\Phi)\right],\qquad(2.6)$$
--   $$\dot H=-\frac{\kappa^2}{2}\left(1+\frac{\kappa^2\Phi^2}{8}\right)\left[\dot\Phi^2-\frac12\frac{H\Phi\dot\Phi}{(1+\kappa^2\Phi^2/8)^2}\right],\qquad(2.7)$$
--   $$H^2=\frac{\kappa^2}{3}\rho,\qquad \dot H=-\frac{\kappa^2}{2}(\rho+p),$$
--   and, if moreover $\dot\Phi(t)\neq0$,
--   $$\ddot\Phi+3H\dot\Phi+V'(\Phi)-\frac34\frac{H^2\Phi}{(1+\kappa^2\Phi^2/8)^2}=0.\qquad(2.8)$$
--
--   This is the reduced dynamical system of Section 2 that the paper integrates numerically for all three cosmological eras.
--
--   **Formalization Note** The hypothesis $\dot\Phi(t)\neq0$ for (2.8) makes explicit the division implicit in "deriving the first equation and using the second one".
-- source:
--   S. H. Pereira and T. M. Guimarães, "From inflation to recent cosmic acceleration: the fermionic Elko field driving the evolution of the universe", JCAP 09 (2017) 038, https://doi.org/10.1088/1475-7516/2017/09/038 (arXiv:1702.07385), p. 5, Section 2, Eqs. (2.2)–(2.10)

import Mathlib

namespace PereiraGuimaraesElko

theorem elko_frw_reduced_dynamics (κ : ℝ) (I : Set ℝ) (hI : IsOpen I) (H h Φ V ρ p : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t) (hΦ : ∀ t ∈ I, DifferentiableAt ℝ Φ t)
    (hΦ' : ∀ t ∈ I, DifferentiableAt ℝ (deriv Φ) t) (hV : Differentiable ℝ V)
    (h25 : ∀ t ∈ I, h t = -(1 / 8) * (κ ^ 2 * Φ t ^ 2 / (1 + κ ^ 2 * Φ t ^ 2 / 8)) * H t)
    (h22 : ∀ t ∈ I, H t ^ 2 = κ ^ 2 / 3 * (deriv Φ t ^ 2 / 2 + V (Φ t)
        + 3 / 8 * H t ^ 2 * Φ t ^ 2 + 3 / 4 * H t * h t * Φ t ^ 2)
        + (1 + κ ^ 2 * Φ t ^ 2 / 8) * h t ^ 2)
    (h23 : ∀ t ∈ I, deriv H t = -(κ ^ 2 / 2) * (deriv Φ t ^ 2 + 3 / 4 * H t * h t * Φ t ^ 2
        - 1 / 4 * deriv (fun s => (H s + h s) * Φ s ^ 2) t)
        - 3 * (1 + κ ^ 2 * Φ t ^ 2 / 8) * h t ^ 2)
    (h29 : ∀ t ∈ I, ρ t = deriv Φ t ^ 2 / 2 + V (Φ t)
        + 3 / 8 * (H t ^ 2 * Φ t ^ 2) / (1 + κ ^ 2 * Φ t ^ 2 / 8))
    (h210 : ∀ t ∈ I, p t = deriv Φ t ^ 2 / 2 - V (Φ t)
        - 3 / 8 * (H t ^ 2 * Φ t ^ 2) / (1 + κ ^ 2 * Φ t ^ 2 / 8)
        - 1 / 4 * (deriv H t * Φ t ^ 2) / (1 + κ ^ 2 * Φ t ^ 2 / 8)
        - 1 / 2 * (H t * Φ t * deriv Φ t) / (1 + κ ^ 2 * Φ t ^ 2 / 8) ^ 2) :
    ∀ t ∈ I,
      H t ^ 2 = κ ^ 2 / 3 * (1 + κ ^ 2 * Φ t ^ 2 / 8) * (deriv Φ t ^ 2 / 2 + V (Φ t)) ∧
      deriv H t = -(κ ^ 2 / 2) * (1 + κ ^ 2 * Φ t ^ 2 / 8) *
          (deriv Φ t ^ 2 - 1 / 2 * (H t * Φ t * deriv Φ t) / (1 + κ ^ 2 * Φ t ^ 2 / 8) ^ 2) ∧
      H t ^ 2 = κ ^ 2 / 3 * ρ t ∧
      deriv H t = -(κ ^ 2 / 2) * (ρ t + p t) ∧
      (deriv Φ t ≠ 0 →
        deriv (deriv Φ) t + 3 * H t * deriv Φ t + deriv V (Φ t)
          - 3 / 4 * (H t ^ 2 * Φ t) / (1 + κ ^ 2 * Φ t ^ 2 / 8) ^ 2 = 0) := by
  sorry

end PereiraGuimaraesElko
