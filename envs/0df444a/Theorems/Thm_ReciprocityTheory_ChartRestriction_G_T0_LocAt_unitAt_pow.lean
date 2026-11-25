-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_LocAt_unitAt_pow
-- name    : ReciprocityTheory.ChartRestriction.G.T0.LocAt.unitAt_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:53:45.077074+00:00
-- url     : https://prove2.me/theorems/af6fe391-3c1d-4b81-b568-036c8e0e2741
-- title:
--   Loc At: unit At pow
-- statement:
--   The Loc At construction uses the unit At pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UnitAtIntAt.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UnitAtIntAt.lean#L74-L77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DiscLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UnitAtIntAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
open ReciprocityTheory.ChartRestriction.G.T0.LocAt
variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
variable {p : Ideal R} [hP : p.IsPrime]
include hP
omit [IsDomain R] [IsFractionRing R F]

theorem ReciprocityTheory.ChartRestriction.G.T0.LocAt.unitAt_pow {x : F} (hx : UnitAt p x) (n : ℕ) : UnitAt p (x ^ n) := by sorry
