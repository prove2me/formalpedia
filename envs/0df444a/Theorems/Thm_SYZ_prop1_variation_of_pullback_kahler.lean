-- Prove2me | Theorems.Thm_SYZ_prop1_variation_of_pullback_kahler
-- name    : SYZ.prop1_variation_of_pullback_kahler
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T03:51:53.247108+00:00
-- url     : https://prove2.me/theorems/a79c96ca-20fc-4a98-84ec-dff175467c6e
-- title:
--   SYZ Proposition 1: $\frac{d}{dt} f^{*}\omega = d\theta$
-- statement:
--   **Proposition 1 of Strominger–Yau–Zaslow.** Let $F$ be a smooth one-parameter family of maps $f_t : \mathbb R^n \to \mathbb C^n$, and let
--   $$\theta(t)_i \;=\; \omega\!\left(\dot f_t,\ \partial_i f_t\right)$$
--   be the $1$-form obtained by contracting the velocity of the family into the Kähler form of $\mathbb C^n$. Then the pullback of the Kähler form varies by an exact form:
--   $$\frac{d}{dt}\,\big(f_t^{*}\omega\big)_{ij} \;=\; \partial_i \theta_j - \partial_j \theta_i \;=\; (d\theta)_{ij}.$$
--
--   Consequently a deformation preserves the Lagrangian condition $f^{*}\omega = 0$ to first order exactly when $\theta$ is a **closed** $1$-form — the first half of the identification of the tangent space to the moduli space of special Lagrangian submanifolds with the harmonic $1$-forms on the brane.
--
--   The identity is purely local and needs no hypothesis beyond smoothness: neither the Lagrangian nor the special Lagrangian condition is assumed.
-- source:
--   A. Strominger, S.-T. Yau, E. Zaslow, "Mirror symmetry is T-duality", Nuclear Physics B 479 (1996) 243-259, doi:10.1016/0550-3213(96)00434-8, arXiv:hep-th/9606040, p. 250, Proposition 1

import Definitions.Def_syz_flat_model

namespace SYZ

theorem prop1_variation_of_pullback_kahler {n : ℕ} (F : ℝ → Dom n → Amb n)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (x : Dom n) (i j : Fin n) :
    deriv (fun s => kForm (D (F s) i x) (D (F s) j x)) t
      = D (fun y => theta1 F t y j) i x - D (fun y => theta1 F t y i) j x := by sorry

end SYZ
