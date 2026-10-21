-- Prove2me | Theorems.Thm_SI_model_faithful
-- name    : SI.model_faithful
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-20T13:56:45.952209+00:00
-- url     : https://prove2.me/theorems/9817de2e-bd5c-48c8-92ac-8da17df9801f
-- title:
--   The quantity model identifies coherent units faithfully
-- statement:
--   Assuming the dimension map of the defining constants is bijective, the
--   identification of coherent units with defining-constant monomials is
--   faithful: two coherent units denoting the same quantity of the
--   defining constants are equal. The seven value postulates together with
--   the unimodularity of the dimension-exponent matrix force the exponent
--   assignment of the model to be the inverse of the dimension map, so a
--   coherent unit is recovered from its image by its dimension and its
--   numerical factor one. This is the formal content of the statement of
--   section 2.2 that the seven defining constants, together with the
--   definitions of the units in which their values are expressed, fix the
--   complete system of units.
-- source:
--   The International System of Units (SI), 9th edition, V4.01 (BIPM, 2026), section 2.2 (the seven defining constants together with the definitions of the units in which they are expressed fix the whole system).

import Mathlib
import Definitions.Def_SI_dim
import Definitions.Def_SI_units
import Definitions.Def_SI_qmodel

/-!
# The quantity model identifies coherent units faithfully

The seven value postulates of Table 1, together with the
unimodularity of the dimension-exponent matrix of the defining
constants, determine the exponent assignment of every quantity model
of the SI: it is the inverse of the dimension map. Consequently the
identification of a coherent unit with its defining-constant monomial
is faithful: two coherent units denoting the same quantity of the
defining constants have the same dimension and the same numerical
factor, hence are the same unit. This is the formal content of the
statement of section 2.2 that the seven defining constants, together
with the definitions of the units in which they are expressed, fix the
complete system. This milestone is proved on the way to the goal
theorem `SI.si_complete`.
-/

namespace SI

/-- In every quantity model of the SI whose dimension map dimOfExpo is
bijective (milestone `SI.dim_basis`), the map identifying a coherent
unit with its defining-constant monomial is injective on coherent
units: two coherent units with the same image are equal. -/
theorem model_faithful (M : SIModel)
    (hbas : Function.Bijective dimOfExpo) :
    ∀ u v : SIUnit, IsCoherent u → IsCoherent v →
      toQ M u = toQ M v → u = v := by
  sorry

end SI
