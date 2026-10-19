-- Prove2me | Theorems.Thm_PereiraGuimaraesElko_raychaudhuri_eq_2_7
-- name    : PereiraGuimaraesElko.raychaudhuri_eq_2_7
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:50:27.198982+00:00
-- url     : https://prove2.me/theorems/500d778f-8808-4f95-a74e-7ae85d06f23e
-- title:
--   Eq. (2.7): eliminating the torsion from the second Friedmann equation (2.3)
-- statement:
--   Let $\kappa\in\mathbb R$, let $I\subseteq\mathbb R$ be an open set of times, and let $H,h,\Phi$ be real functions with $H$ and $\Phi$ differentiable on $I$. Assume that $h$ is given on $I$ by the torsion relation (2.5), $h=-\frac18\frac{\kappa^2\Phi^2}{1+\kappa^2\Phi^2/8}H$. Then for every $t\in I$ the second Friedmann equation (2.3),
--   $$\dot H=-\frac{\kappa^2}{2}\left[\dot\Phi^2+\frac34Hh\Phi^2-\frac14\frac{d}{dt}\big[(H+h)\Phi^2\big]\right]-3\left(1+\frac{\kappa^2\Phi^2}{8}\right)h^2,$$
--   holds at $t$ if and only if
--   $$\dot H=-\frac{\kappa^2}{2}\left(1+\frac{\kappa^2\Phi^2}{8}\right)\left[\dot\Phi^2-\frac12\,\frac{H\Phi\dot\Phi}{(1+\kappa^2\Phi^2/8)^2}\right]\qquad(2.7)$$
--   holds at $t$.
--
--   Note that (2.3) contains $\dot H$ on both sides (through $\frac{d}{dt}[(H+h)\Phi^2]$); (2.7) is the explicit form.
--
--   **Formalization Note** The source states the direction (2.3) $\Rightarrow$ (2.7); the converse also holds and is included.
-- source:
--   S. H. Pereira and T. M. Guimarães, "From inflation to recent cosmic acceleration: the fermionic Elko field driving the evolution of the universe", JCAP 09 (2017) 038, https://doi.org/10.1088/1475-7516/2017/09/038 (arXiv:1702.07385), p. 5, Eqs. (2.3), (2.5), (2.7)

import Mathlib

namespace PereiraGuimaraesElko

theorem raychaudhuri_eq_2_7 (κ : ℝ) (I : Set ℝ) (hI : IsOpen I) (H h Φ : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t) (hΦ : ∀ t ∈ I, DifferentiableAt ℝ Φ t)
    (h25 : ∀ t ∈ I, h t = -(1 / 8) * (κ ^ 2 * Φ t ^ 2 / (1 + κ ^ 2 * Φ t ^ 2 / 8)) * H t) :
    ∀ t ∈ I,
      (deriv H t = -(κ ^ 2 / 2) * (deriv Φ t ^ 2 + 3 / 4 * H t * h t * Φ t ^ 2
          - 1 / 4 * deriv (fun s => (H s + h s) * Φ s ^ 2) t)
          - 3 * (1 + κ ^ 2 * Φ t ^ 2 / 8) * h t ^ 2 ↔
        deriv H t = -(κ ^ 2 / 2) * (1 + κ ^ 2 * Φ t ^ 2 / 8) *
          (deriv Φ t ^ 2 - 1 / 2 * (H t * Φ t * deriv Φ t) / (1 + κ ^ 2 * Φ t ^ 2 / 8) ^ 2)) := by
  sorry

end PereiraGuimaraesElko
