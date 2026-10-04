-- Prove2me | Theorems.Thm_VaryingConstants_natural_unit_values_independent_of_units
-- name    : VaryingConstants.natural_unit_values_independent_of_units
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T02:26:34.053986+00:00
-- url     : https://prove2.me/theorems/d10f0a37-4bac-4ac0-96d9-b77149d44abd
-- title:
--   Values in natural units do not depend on the starting system of units
-- statement:
--   Let $D\in\mathbb R^{n\times d}$ and let $e_1,\dots,e_d$ be constants with $\det D_e\neq0$ (as in the natural-units milestone). Let $x\in\mathbb R^n_{>0}$ and let $r\in\mathbb R^d_{>0}$ be any change of units, giving the configuration $r\cdot x$. If $s$ is a system of natural units for $x$ and $s'$ is a system of natural units for $r\cdot x$, then
--   $$ s'\cdot(r\cdot x) \;=\; s\cdot x . $$
--
--   So the numerical value of **every** constant expressed in natural units is the same whatever system of units one started from: in natural units all constants are dimensionless numbers.
-- source:
--   J.-P. Uzan, "Varying Constants, Gravitation and Cosmology", Living Rev. Relativity 14 (2011) 2, http://www.livingreviews.org/lrr-2011-2, §2.1.1 "Fundamental parameters", p. 17: "Once a set of three independent constants has been chosen as natural units, then all other constants are dimensionless quantities. The values of these combinations of constants does not depend on ... the definition of the units".

import Mathlib
import Definitions.Def_VaryingConstants_units

namespace VaryingConstants

theorem natural_unit_values_independent_of_units {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ)
    (e : Fin d → Fin n) (he : (D.submatrix e id).det ≠ 0)
    (x : Fin n → ℝ) (hx : IsPositive x) (r : Fin d → ℝ) (hr : IsPositive r)
    (s s' : Fin d → ℝ) (hs : IsNaturalUnitsFor D e x s)
    (hs' : IsNaturalUnitsFor D e (unitRescale D r x) s') :
    unitRescale D s' (unitRescale D r x) = unitRescale D s x := by sorry

end VaryingConstants
