-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_unitaryTransvection_zero_first
-- name    : ReciprocityTheory.ChartRestriction.G.SA.unitaryTransvection_zero_first
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:35:01.442419+00:00
-- url     : https://prove2.me/theorems/99cd2d57-8fd1-581b-8e89-9e810c9b6c63
-- title:
--   SA: unitary Transvection zero first
-- statement:
--   The SA construction uses the unitary Transvection zero first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/UnitaryTransvectionZeroSecondMemClosure.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/UnitaryTransvectionZeroSecondMemClosure.lean#L80-L86

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

theorem ReciprocityTheory.ChartRestriction.G.SA.unitaryTransvection_zero_first (e f : ι → K) (c : K) : eich σ J e 0 c = hm σ J e f !![1, c; 0, 1] := by sorry
