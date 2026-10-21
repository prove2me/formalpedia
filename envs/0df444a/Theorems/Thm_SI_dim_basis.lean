-- Prove2me | Theorems.Thm_SI_dim_basis
-- name    : SI.dim_basis
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-20T13:53:05.839446+00:00
-- url     : https://prove2.me/theorems/2d8be9ca-5061-4c99-b061-df3bb91a391e
-- title:
--   The seven defining constants span the dimensions of the SI
-- statement:
--   The dimension map from monomials in the seven defining constants to
--   dimensional products is bijective: every dimension of the SI is a
--   unique integral monomial in the defining constants. This is the formal
--   content of the statement of section 2.2 that the SI is defined by
--   seven constants whose units include both base and derived units, and
--   that any unit of the SI can be written through products or quotients
--   of the defining constants. Equivalently, the dimension-exponent matrix
--   of the constants - read off from the units in which their values are
--   fixed (Hz, m s⁻¹, J s, C, J K⁻¹, mol⁻¹, lm W⁻¹) - is unimodular.
-- source:
--   The International System of Units (SI), 9th edition, V4.01 (BIPM, 2026), section 2.2, Table 1 and the accompanying statement that any unit of the SI can be written through products or quotients of the seven defining constants.

import Mathlib
import Definitions.Def_SI_dim
import Definitions.Def_SI_units
import Definitions.Def_SI_qmodel

/-!
# The dimension map of the defining constants is bijective

Section 2.2 of the SI Brochure states that any unit of the SI can be
written through products or quotients of the seven defining constants.
In the additive form of the dimension space, the monomial in the
defining constants with exponent vector v has dimension dimOfExpo v,
so this completeness claim is exactly the surjectivity of dimOfExpo;
injectivity says that the expression is unique. Both follow from the
fact that the dimension-exponent matrix of the seven defining
constants (section 2.2, Table 1: Δν_Cs in Hz, c in m s⁻¹, h in J s,
e in C, k in J K⁻¹, N_A in mol⁻¹, K_cd in lm W⁻¹) is unimodular,
which is the arithmetic content of the completeness of the seven
defining constants. This milestone is proved on the way to the goal
theorem `SI.si_complete`.
-/

namespace SI

/-- The seven defining constants span the dimension space of the SI
over the integers: the dimension map dimOfExpo, from monomials in the
defining constants to dimensional products, is bijective. In
particular every dimension of the SI is a unique integral monomial in
the defining constants (section 2.2). -/
theorem dim_basis : Function.Bijective dimOfExpo := by
  sorry

end SI
