-- Prove2me | Theorems.Thm_SI_coherent_derived_22
-- name    : SI.coherent_derived_22
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-20T13:53:49.50297+00:00
-- url     : https://prove2.me/theorems/fab444e1-0102-49a5-959d-cf57412162d6
-- title:
--   Coherence of the 22 derived units with special names
-- statement:
--   Each of the 22 coherent derived units with special names (Table 4) is
--   coherent: its numerical factor, as a product of powers of the base
--   units, is one. The sixteen units with a nontrivial dimensional
--   expression have the recorded dimension vectors in the seven base
--   quantities, in the Table 3 order (time, length, mass, electric current,
--   thermodynamic temperature, amount of substance, luminous intensity).
--   The identifications of Table 4 and its notes hold: the radian and the
--   steradian are the unit one (notes b and c), the becquerel is the
--   hertz (distinguished only by usage), the degree Celsius is equal in
--   magnitude to the kelvin, and the gray is the sievert (distinguished
--   only by usage).
-- source:
--   The International System of Units (SI), 9th edition, V4.01 (BIPM, 2026), section 2.3.4 with Table 4 (the 22 coherent derived units with special names, their expressions in base units, and notes b and c) and section 2.3.3, Table 3 (the dimension symbols).

import Mathlib
import Definitions.Def_SI_dim
import Definitions.Def_SI_units
import Definitions.Def_SI_qmodel

/-!
# Coherence of the 22 derived units with special names

Section 2.3.4 of the SI Brochure: a coherent derived unit is a product
of powers of the base units with numerical factor one; Table 4 lists
the 22 coherent derived units with special names and symbols, each
with its expression in terms of the base units. This milestone
records, for each of the 22 units, the coherence of its numerical
factor and, for the sixteen units with a nontrivial dimensional
expression, its dimension vector in the base quantities (section
2.3.3, Table 3). It also records the identifications stated in
Table 4 and its notes: the radian and the steradian are the unit one
written with angle symbols (notes b and c), the becquerel and the
hertz are both s⁻¹ (distinguished by usage), the degree Celsius is
equal in magnitude to the kelvin, and the gray and the sievert are
both J kg⁻¹ (distinguished by usage). This milestone is proved on the
way to the goal theorem `SI.si_complete`.
-/

namespace SI

/-- The 22 derived units with special names (Table 4) are coherent,
sixteen of them have the recorded base-dimension vectors (Table 3
order: time, length, mass, electric current, thermodynamic
temperature, amount of substance, luminous intensity), and the
identifications of Table 4 hold: radian and steradian are the unit
one, becquerel is hertz, degree Celsius is the kelvin, and gray is
sievert. -/
theorem coherent_derived_22 :
    (∀ u ∈ named22, IsCoherent u) ∧
    newton.dim = ![-2, 1, 1, 0, 0, 0, 0] ∧
    pascal.dim = ![-2, -1, 1, 0, 0, 0, 0] ∧
    joule.dim = ![-2, 2, 1, 0, 0, 0, 0] ∧
    watt.dim = ![-3, 2, 1, 0, 0, 0, 0] ∧
    coulomb.dim = ![1, 0, 0, 1, 0, 0, 0] ∧
    volt.dim = ![-3, 2, 1, -1, 0, 0, 0] ∧
    farad.dim = ![4, -2, -1, 2, 0, 0, 0] ∧
    ohm.dim = ![-3, 2, 1, -2, 0, 0, 0] ∧
    siemens.dim = ![3, -2, -1, 2, 0, 0, 0] ∧
    weber.dim = ![-2, 2, 1, -1, 0, 0, 0] ∧
    tesla.dim = ![-2, 0, 1, -1, 0, 0, 0] ∧
    henry.dim = ![-2, 2, 1, -2, 0, 0, 0] ∧
    lumen.dim = ![0, 0, 0, 0, 0, 0, 1] ∧
    lux.dim = ![0, -2, 0, 0, 0, 0, 1] ∧
    gray.dim = ![0, 2, 0, 0, 0, 0, 0] ∧
    katal.dim = ![-1, 0, 0, 0, 0, 1, 0] ∧
    radian = uone ∧
    steradian = uone ∧
    becquerel = hertz ∧
    celsius = kelvin ∧
    gray = sievert := by
  sorry

end SI
