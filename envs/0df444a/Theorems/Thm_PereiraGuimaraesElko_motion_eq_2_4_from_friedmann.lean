-- Prove2me | Theorems.Thm_PereiraGuimaraesElko_motion_eq_2_4_from_friedmann
-- name    : PereiraGuimaraesElko.motion_eq_2_4_from_friedmann
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:49:36.994349+00:00
-- url     : https://prove2.me/theorems/0ac341ed-01e3-4307-a16d-ab07cf1f141a
-- title:
--   Eq. (2.4): the Elko motion equation follows from differentiating (2.2) and using (2.3)
-- statement:
--   Let $\kappa\in\mathbb R$, let $I\subseteq\mathbb R$ be an open set of times, and let $H,h,\Phi,V$ be real functions with $H$, $\Phi$ and $\dot\Phi$ differentiable on $I$ and $V$ differentiable on $\mathbb R$. Assume that for every $t\in I$:
--
--   1. the torsion function is given by (2.5), $h=-\dfrac18\dfrac{\kappa^2\Phi^2}{1+\kappa^2\Phi^2/8}\,H$;
--   2. the first Friedmann equation (2.2) holds;
--   3. the second Friedmann equation (2.3) holds.
--
--   Then at every $t\in I$ with $\dot\Phi(t)\neq0$,
--   $$
--   \ddot\Phi+3H\dot\Phi+V'(\Phi)-\frac34(H+h)^2\Phi=0.\qquad(2.4)
--   $$
--
--   So the motion equation of the Elko field is not an independent postulate: it is a consequence of the two Friedmann equations wherever the field is not momentarily at rest.
--
--   **Formalization Note** The source obtains (2.4) "by deriving the first equation and using the second one", which divides by $\dot\Phi$; the hypothesis $\dot\Phi(t)\neq0$ makes this explicit. Where $\dot\Phi$ vanishes on an interval, (2.2)–(2.3) do not determine $\ddot\Phi$.
-- source:
--   S. H. Pereira and T. M. Guimarães, "From inflation to recent cosmic acceleration: the fermionic Elko field driving the evolution of the universe", JCAP 09 (2017) 038, https://doi.org/10.1088/1475-7516/2017/09/038 (arXiv:1702.07385), p. 5, Eqs. (2.2)–(2.5) and the sentence introducing (2.4)

import Mathlib

namespace PereiraGuimaraesElko

theorem motion_eq_2_4_from_friedmann (κ : ℝ) (I : Set ℝ) (hI : IsOpen I) (H h Φ V : ℝ → ℝ)
    (hH : ∀ t ∈ I, DifferentiableAt ℝ H t) (hΦ : ∀ t ∈ I, DifferentiableAt ℝ Φ t)
    (hΦ' : ∀ t ∈ I, DifferentiableAt ℝ (deriv Φ) t) (hV : Differentiable ℝ V)
    (h25 : ∀ t ∈ I, h t = -(1 / 8) * (κ ^ 2 * Φ t ^ 2 / (1 + κ ^ 2 * Φ t ^ 2 / 8)) * H t)
    (h22 : ∀ t ∈ I, H t ^ 2 = κ ^ 2 / 3 * (deriv Φ t ^ 2 / 2 + V (Φ t)
        + 3 / 8 * H t ^ 2 * Φ t ^ 2 + 3 / 4 * H t * h t * Φ t ^ 2)
        + (1 + κ ^ 2 * Φ t ^ 2 / 8) * h t ^ 2)
    (h23 : ∀ t ∈ I, deriv H t = -(κ ^ 2 / 2) * (deriv Φ t ^ 2 + 3 / 4 * H t * h t * Φ t ^ 2
        - 1 / 4 * deriv (fun s => (H s + h s) * Φ s ^ 2) t)
        - 3 * (1 + κ ^ 2 * Φ t ^ 2 / 8) * h t ^ 2) :
    ∀ t ∈ I, deriv Φ t ≠ 0 →
      deriv (deriv Φ) t + 3 * H t * deriv Φ t + deriv V (Φ t)
        - 3 / 4 * (H t + h t) ^ 2 * Φ t = 0 := by
  sorry

end PereiraGuimaraesElko
