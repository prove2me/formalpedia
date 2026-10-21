-- Prove2me | Theorems.Thm_SI_base_unit_inversions
-- name    : SI.base_unit_inversions
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-20T13:55:29.378379+00:00
-- url     : https://prove2.me/theorems/db2c70ab-23a7-4e2f-b696-16c61d293c8f
-- title:
--   The base units in terms of the defining constants
-- statement:
--   In every quantity model of the SI, the seven base units are the exact
--   defining-constant monomials of section 2.3.1:
--   1 s = 9 192 631 770 / Δν_Cs;
--   1 m = (9 192 631 770 / 299 792 458) c/Δν_Cs;
--   1 kg = (299 792 458)² / ((6.626 070 15 × 10⁻³⁴)(9 192 631 770))
--     h Δν_Cs / c²;
--   1 A = Δν_Cs e / ((9 192 631 770)(1.602 176 634 × 10⁻¹⁹));
--   1 K = (1.380 649 × 10⁻²³) / ((6.626 070 15 × 10⁻³⁴)(9 192 631 770))
--     Δν_Cs h / k;
--   1 mol = 6.022 140 76 × 10²³ / N_A;
--   1 cd = (Δν_Cs)² h K_cd /
--     ((6.626 070 15 × 10⁻³⁴)(9 192 631 770)² 683).
--   These follow from the seven defining statements of Table 1 alone,
--   through the homomorphism properties of the model.
-- source:
--   The International System of Units (SI), 9th edition, V4.01 (BIPM, 2026), section 2.3.1 (the seven base units expressed through the defining constants).

import Mathlib
import Definitions.Def_SI_dim
import Definitions.Def_SI_units
import Definitions.Def_SI_qmodel

/-!
# The base units in terms of the defining constants

Section 2.3.1 of the SI Brochure prints, for each of the seven base
units, its expression in terms of the defining constants:
1 s = 9 192 631 770 / Δν_Cs,
1 m = (9 192 631 770 / 299 792 458) c / Δν_Cs,
1 kg = (299 792 458)² / ((6.626 070 15 × 10⁻³⁴)(9 192 631 770))
  h Δν_Cs / c²,
1 A = Δν_Cs e / ((9 192 631 770)(1.602 176 634 × 10⁻¹⁹)),
1 K = (1.380 649 × 10⁻²³) / ((6.626 070 15 × 10⁻³⁴)(9 192 631 770))
  Δν_Cs h / k,
1 mol = 6.022 140 76 × 10²³ / N_A, and
1 cd = (Δν_Cs)² h K_cd /
  ((6.626 070 15 × 10⁻³⁴)(9 192 631 770)² 683).
This milestone derives these seven inversions from the seven defining
statements of Table 1 alone, in any quantity model of the SI. This
milestone is proved on the way to the goal theorem `SI.si_complete`.
-/

namespace SI

/-- In every quantity model of the SI, the seven base units are the
exact defining-constant monomials of section 2.3.1. -/
theorem base_unit_inversions (M : SIModel) :
    toQ M second = sMono ∧
    toQ M metre = mMono ∧
    toQ M kilogram = kgMono ∧
    toQ M ampere = AMono ∧
    toQ M kelvin = KMono ∧
    toQ M mole = molMono ∧
    toQ M candela = cdMono := by
  sorry

end SI
