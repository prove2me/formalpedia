-- Prove2me | Theorems.Thm_SI_prefixes_and_exact_non_si
-- name    : SI.prefixes_and_exact_non_si
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-20T13:54:35.23222+00:00
-- url     : https://prove2.me/theorems/dbe3771d-e2b4-4ed4-9bda-de230634c8ea
-- title:
--   Decimal prefixes and the exact non-SI conversions
-- statement:
--   Decimal prefixes compose by adding exponents, and exact powers of ten
--   never vanish. The kilogram, which carries a prefix in its name,
--   receives its decimal multiples and submultiples on the gram:
--   prefixed 3 gram = kilogram. The non-SI units exactly accepted for use
--   with the SI (Table 8) whose defining factors are exact numerical
--   factors have the recorded conversions: the tonne is the megagram,
--   the bar is prefixed 5 pascal, the hour is 60 minutes, the day is
--   24 hours, the litre is the cubic decimetre, the astronomical unit is
--   149 597 870 700 m, the nautical mile is 1852 m, and the knot is
--   (1852/3600) m s⁻¹.
-- source:
--   The International System of Units (SI), 9th edition, V4.01 (BIPM, 2026), chapter 3 (decimal prefixes; the gram rule for the kilogram) and chapter 4, Table 8 (non-SI units accepted for use with the SI, with their exact defining factors).

import Mathlib
import Definitions.Def_SI_dim
import Definitions.Def_SI_units
import Definitions.Def_SI_qmodel

/-!
# Decimal prefixes and the exact non-SI conversions

Chapter 3 of the SI Brochure fixes the decimal prefixes and the rule
that compound prefixes are not permitted; Table 8 lists the non-SI
units exactly accepted for use with the SI. Those with definitions
given by an exact numerical factor are: the minute, hour and day of
time; the litre; the tonne; the bar; the astronomical unit; the
nautical mile and the knot; and the electronvolt (its exactness is
the subject of a separate milestone). The prefixes compose according
to the addition of exponents, and the kilogram, which carries a
prefix in its name, receives its further prefixes on the gram. This
milestone is proved on the way to the goal theorem `SI.si_complete`.
-/

namespace SI

/-- Decimal prefixes compose by adding exponents, exact powers of ten
never vanish, the kilogram is the kilo-gram, and the exact non-SI
units of Table 8 have the recorded exact conversions: the tonne is
the megagram, the bar is 10⁵ Pa, the hour is 60 minutes, the day is
24 hours, the litre is the cubic decimetre, the astronomical unit is
149 597 870 700 m, the nautical mile is 1852 m, and the knot is
(1852/3600) m s⁻¹. -/
theorem prefixes_and_exact_non_si :
    (∀ k l : ℤ, ∀ u : SIUnit, prefixed k (prefixed l u) = prefixed (k + l) u) ∧
    (∀ k : ℤ, pow10 k ≠ 0) ∧
    prefixed 3 gram = kilogram ∧
    tonne = prefixed 6 gram ∧
    bar = prefixed 5 pascal ∧
    hour = uscale 60 minute ∧
    day = uscale 24 hour ∧
    litre = umul (prefixed (-1) metre)
      (umul (prefixed (-1) metre) (prefixed (-1) metre)) ∧
    au = uscale 149597870700 metre ∧
    nauticalMile = uscale 1852 metre ∧
    knot = uscale (1852 / 3600) (udiv metre second) := by
  sorry

end SI
