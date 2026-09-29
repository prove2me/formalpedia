-- Prove2me | Theorems.Thm_SYZ_prop2_variation_of_pullback_kappa_oriented
-- name    : SYZ.prop2_variation_of_pullback_kappa_oriented
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-24T04:10:31.037445+00:00
-- url     : https://prove2.me/theorems/b34048a1-ff0d-4499-bbcf-a2e24461545d
-- title:
--   SYZ Proposition 2: $\frac{d}{dt} f^{*}\kappa = -\,d(\ast\theta)$ for the calibrated orientation
-- statement:
--   **Proposition 2 of Strominger–Yau–Zaslow, with the calibrated orientation.** Let $F$ be a smooth one-parameter family of maps $f_t : \mathbb R^n \to \mathbb C^n$, and suppose that at the parameter value $t$ the map $f_t$ is a special Lagrangian immersion at every point, oriented by the calibration: $\operatorname{Re}\Omega(\partial_1 f_t,\dots,\partial_n f_t) > 0$, so that $\operatorname{Re}\Omega$ restricts to the volume form of $f_t$ (the orientation half of Harvey and Lawson's definition). With $\theta_i = \omega(\dot f_t, \partial_i f_t)$ as in Proposition 1, the pullback of $\kappa = \operatorname{Im}\Omega$ varies by
--   $$\frac{d}{dt}\,f_t^{*}\kappa \;=\; -\,d\!\left(\ast\,\theta\right),$$
--   written out in coordinates as
--   $$\frac{d}{dt}\,\kappa\big(\partial_1 f_t,\dots,\partial_n f_t\big) \;=\; -\sum_i \partial_i\!\left(\sqrt{\det g}\;\sum_j g^{ij}\,\theta_j\right),$$
--   where $g_{ij}$ is the induced metric of $f_t$.
--
--   Since the right-hand side is $(d^{\dagger}\theta)\,\mathrm{dvol}$ up to sign, the deformation preserves the special Lagrangian condition $f^{*}\kappa = 0$ to first order exactly when $\theta$ is co-closed; together with Proposition 1 this identifies the tangent space to the moduli space of special Lagrangian deformations with the harmonic $1$-forms on the brane.
--
--   The orientation hypothesis is needed for the sign: $\operatorname{Im}\Omega = 0$ alone allows both orientations of a special Lagrangian plane, and reversing the orientation reverses the sign of the right-hand side (for $n = 1$, $f_t(x) = -x + itx$ gives $+1$ on the left and $-1$ on the right). The special Lagrangian hypothesis is essential as well: for a merely Lagrangian $f_t$ the identity acquires an additional term proportional to the Lagrangian angle.
-- source:
--   A. Strominger, S.-T. Yau, E. Zaslow, "Mirror symmetry is T-duality", Nuclear Physics B 479 (1996) 243-259, doi:10.1016/0550-3213(96)00434-8, arXiv:hep-th/9606040, p. 250, Proposition 2 (proof referred to McLean, reference [7] of the paper); orientation convention from R. Harvey and H. B. Lawson, Calibrated geometries, Acta Math. 148 (1982), Definition III.1.2.

import Definitions.Def_syz_flat_model

namespace SYZ

theorem prop2_variation_of_pullback_kappa_oriented {n : ℕ} (F : ℝ → Dom n → Amb n)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (t : ℝ) (hSL : ∀ y, IsSpecialLagrangianAt (F t) y)
    (him : ∀ y, (gInd (F t) y).det ≠ 0)
    (hor : ∀ y, 0 < (hVol (fun i => D (F t) i y)).re) (x : Dom n) :
    deriv (fun s => kappa (fun i => D (F s) i x)) t
      = -∑ i, D (fun y => volDens (F t) y
          * ∑ j, (gInd (F t) y)⁻¹ i j * theta1 F t y j) i x := by sorry

end SYZ
