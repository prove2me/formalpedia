-- Prove2me | Theorems.Thm_VaryingConstants_same_dimensionless_iff_unit_change
-- name    : VaryingConstants.same_dimensionless_iff_unit_change
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T02:50:41.817149+00:00
-- url     : https://prove2.me/theorems/21f0b9d7-4aaa-4428-8ca8-2d3677c262f5
-- title:
--   Equal dimensionless combinations $\iff$ related by a change of units
-- statement:
--   Let $D\in\mathbb R^{n\times d}$ be a dimension matrix and let $x,y\in\mathbb R^n_{>0}$ be two positive configurations of the constants. Then
--   $$ \Big(\forall a\in\mathcal Z_D:\ \prod_i x_i^{a_i}=\prod_i y_i^{a_i}\Big) \iff \exists\, s\in\mathbb R^d_{>0}:\ y_i=x_i\prod_j s_j^{D_{ij}}\ \ \forall i . $$
--
--   The direction $(\Rightarrow)$ is Uzan's statement that a variation of the constants that leaves all dimensionless numbers unchanged is just a redefinition of units; $(\Leftarrow)$ says that a redefinition of units leaves all dimensionless numbers unchanged.
-- source:
--   J.-P. Uzan, "Varying Constants, Gravitation and Cosmology", Living Rev. Relativity 14 (2011) 2, http://www.livingreviews.org/lrr-2011-2, §2.1.1 "Fundamental parameters", p. 17: "any variation of constants that will leave these numbers unaffected is actually just a redefinition of units."

import Mathlib
import Definitions.Def_VaryingConstants_units

namespace VaryingConstants

theorem same_dimensionless_iff_unit_change {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ)
    (x y : Fin n → ℝ) (hx : IsPositive x) (hy : IsPositive y) :
    (∀ a ∈ dimensionlessExponents D, powerMonomial a x = powerMonomial a y) ↔
      ∃ s : Fin d → ℝ, IsPositive s ∧ y = unitRescale D s x := by sorry

end VaryingConstants
