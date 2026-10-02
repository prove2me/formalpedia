-- Prove2me | Theorems.Thm_VaryingConstants_only_dimensionless_variations_measurable
-- name    : VaryingConstants.only_dimensionless_variations_measurable
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T03:06:36.031202+00:00
-- url     : https://prove2.me/theorems/cc54b262-45f7-4ac0-afa2-2ccbfc843dab
-- title:
--   Only variations of dimensionless constants can be measured
-- statement:
--   Let $D\in\mathbb R^{n\times d}$ be a dimension matrix and let $f:\mathbb R^n\to\mathbb R$ be a unit-invariant observable: $f(s\cdot x)=f(x)$ for all positive $x$ and all positive changes of units $s$. If $x,y\in\mathbb R^n_{>0}$ satisfy
--   $$ \prod_i x_i^{a_i}=\prod_i y_i^{a_i}\qquad\text{for every } a\in\mathcal Z_D, $$
--   then
--   $$ f(x)=f(y). $$
--
--   This is the formal content of Uzan's remark that only the variation of dimensionless constants can be measured: a change of the dimensional constants that leaves every dimensionless combination fixed is invisible to every measurement outcome.
-- source:
--   J.-P. Uzan, "Varying Constants, Gravitation and Cosmology", Living Rev. Relativity 14 (2011) 2, http://www.livingreviews.org/lrr-2011-2, §2.1.2 "Constants and metrology", p. 14: "This implies that only the variation of dimensionless constants can be measured".

import Mathlib
import Definitions.Def_VaryingConstants_units

namespace VaryingConstants

theorem only_dimensionless_variations_measurable {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : IsUnitInvariant D f)
    (x y : Fin n → ℝ) (hx : IsPositive x) (hy : IsPositive y)
    (hxy : ∀ a ∈ dimensionlessExponents D, powerMonomial a x = powerMonomial a y) :
    f x = f y := by sorry

end VaryingConstants
