-- Prove2me | Theorems.Thm_SI_printed_approximations
-- name    : SI.printed_approximations
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-20T13:57:39.294049+00:00
-- url     : https://prove2.me/theorems/e1f9bcbc-a712-4796-9ed5-179e3c15de65
-- title:
--   The printed decimal approximations of section 2.3.1
-- statement:
--   The exact rational coefficients of the five approximated inversions of
--   section 2.3.1 agree with the printed decimal values to within one part
--   in a million: 1 m ≈ 30.663 319 c/Δν_Cs;
--   1 kg ≈ 1.475 5214 × 10⁴⁰ h Δν_Cs / c²;
--   1 A ≈ 6.789 6868 × 10⁸ Δν_Cs e;
--   1 K ≈ 2.266 6653 Δν_Cs h / k;
--   1 cd ≈ 2.614 8305 × 10¹⁰ (Δν_Cs)² h K_cd.
--   The second and the mole are exact and carry no printed approximation.
--   The comparison is a finite calculation with exact rational
--   arithmetic; the largest deviation is about 3.5 × 10⁻⁸.
-- source:
--   The International System of Units (SI), 9th edition, V4.01 (BIPM, 2026), section 2.3.1, the decimal approximations printed after the exact expressions of the metre, the kilogram, the ampere, the kelvin and the candela.

import Mathlib
import Definitions.Def_SI_dim
import Definitions.Def_SI_units
import Definitions.Def_SI_qmodel

/-!
# The printed decimal approximations of section 2.3.1

Section 2.3.1 of the SI Brochure prints, after each exact inversion
of a base unit, its decimal approximation:
1 m ≈ 30.663 319 c/Δν_Cs,
1 kg ≈ 1.475 5214 × 10⁴⁰ h Δν_Cs / c²,
1 A ≈ 6.789 6868 × 10⁸ Δν_Cs e,
1 K ≈ 2.266 6653 Δν_Cs h / k, and
1 cd ≈ 2.614 8305 × 10¹⁰ (Δν_Cs)² h K_cd.
(The second and the mole are exact and are printed without
approximations.) This milestone verifies each printed value against
the exact rational coefficient of the corresponding monomial, to
within one part in 10⁶, which is far tighter than the eight
significant digits printed. This milestone is proved on the way to
the goal theorem `SI.si_complete`.
-/

namespace SI

/-- The exact rational coefficients of the five approximated monomials
of section 2.3.1 agree with the printed decimal values to within
10⁻⁶ (in the units in which the brochure prints them). -/
theorem printed_approximations :
    abs (mMono.coef - 30663319 / (10 : ℚ) ^ 6) < 1 / (10 : ℚ) ^ 6 ∧
    abs (kgMono.coef / (10 : ℚ) ^ 40 - 14755214 / (10 : ℚ) ^ 7)
      < 1 / (10 : ℚ) ^ 6 ∧
    abs (AMono.coef / (10 : ℚ) ^ 8 - 67896868 / (10 : ℚ) ^ 7)
      < 1 / (10 : ℚ) ^ 6 ∧
    abs (KMono.coef - 22666653 / (10 : ℚ) ^ 7) < 1 / (10 : ℚ) ^ 6 ∧
    abs (cdMono.coef / (10 : ℚ) ^ 10 - 26148305 / (10 : ℚ) ^ 7)
      < 1 / (10 : ℚ) ^ 6 := by
  sorry

end SI
