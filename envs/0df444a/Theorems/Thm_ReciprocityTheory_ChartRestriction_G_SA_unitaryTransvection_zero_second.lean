-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_unitaryTransvection_zero_second
-- name    : ReciprocityTheory.ChartRestriction.G.SA.unitaryTransvection_zero_second
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:39.659691+00:00
-- url     : https://prove2.me/theorems/8e82c22c-56e8-4c80-908b-69efb26b647f
-- title:
--   SA: unitary Transvection zero second
-- statement:
--   The SA construction uses the unitary Transvection zero second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/UnitaryTransvectionZeroSecondMemClosure.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/UnitaryTransvectionZeroSecondMemClosure.lean#L89-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_UnitaryTransvectionZeroSecondMemClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (σ J)

theorem ReciprocityTheory.ChartRestriction.G.SA.unitaryTransvection_zero_second (e f : ι → K) (c : K) : eich σ J f 0 c = hm σ J e f !![1, 0; c, 1] := by sorry
