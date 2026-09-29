-- Prove2me | Theorems.Thm_SYZ_prop2_variation_of_pullback_kappa
-- name    : SYZ.prop2_variation_of_pullback_kappa
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-15T03:54:01.575956+00:00
-- url     : https://prove2.me/theorems/dc343d6f-2509-4963-9d64-3aed0c009439
-- title:
--   SYZ Proposition 2: $\frac{d}{dt} f^{*}\kappa = -\,d(\ast\theta)$
-- statement:
--   **Proposition 2 of Strominger–Yau–Zaslow.** Let $F$ be a smooth one-parameter family of maps $f_t : \mathbb R^n \to \mathbb C^n$, and suppose that at the parameter value $t$ the map $f_t$ is a special Lagrangian immersion at every point. With $\theta_i = \omega(\dot f_t, \partial_i f_t)$ as in Proposition 1, the pullback of $\kappa = \operatorname{Im}\Omega$ varies by
--   $$\frac{d}{dt}\,f_t^{*}\kappa \;=\; -\,d\!\left(\ast\,\theta\right),$$
--   written out in coordinates as
--   $$\frac{d}{dt}\,\kappa\big(\partial_1 f_t,\dots,\partial_n f_t\big) \;=\; -\sum_i \partial_i\!\left(\sqrt{\det g}\;\sum_j g^{ij}\,\theta_j\right),$$
--   where $g_{ij}$ is the induced metric of $f_t$.
--
--   Since the right-hand side is $(d^{\dagger}\theta)\,\mathrm{dvol}$ up to sign, the deformation preserves the special Lagrangian condition $f^{*}\kappa = 0$ to first order exactly when $\theta$ is **co-closed**. Together with Proposition 1 this identifies the tangent space to the moduli space of special Lagrangian deformations with the harmonic $1$-forms on the brane.
--
--   The special Lagrangian hypothesis is essential: for a merely Lagrangian $f_t$ the identity acquires an additional term proportional to the Lagrangian angle.
-- source:
--   A. Strominger, S.-T. Yau, E. Zaslow, "Mirror symmetry is T-duality", Nuclear Physics B 479 (1996) 243-259, doi:10.1016/0550-3213(96)00434-8, arXiv:hep-th/9606040, p. 250, Proposition 2 (proof referred to McLean, reference [7] of the paper)

import Definitions.Def_syz_flat_model

namespace SYZ

theorem prop2_variation_of_pullback_kappa {n : ℕ} (F : ℝ → Dom n → Amb n)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (hSL : ∀ y, IsSpecialLagrangianAt (F t) y)
    (him : ∀ y, (gInd (F t) y).det ≠ 0) (x : Dom n) :
    deriv (fun s => kappa (fun i => D (F s) i x)) t
      = -∑ i, D (fun y => volDens (F t) y
          * ∑ j, (gInd (F t) y)⁻¹ i j * theta1 F t y j) i x := by sorry

end SYZ
