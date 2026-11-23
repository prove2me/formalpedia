-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_harmSecond_holds
-- name    : ReciprocityTheory.ChartRestriction.G.TB.harmSecond_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:00.189848+00:00
-- url     : https://prove2.me/theorems/2f4db112-894a-4995-92eb-5241292125fa
-- title:
--   TB: harm Second holds
-- statement:
--   The TB construction uses the harm Second holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HarmSecond.lean#L23-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HarmSecond.lean#L23-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB

theorem ReciprocityTheory.ChartRestriction.G.TB.harmSecond_holds : HarmSecondSt := by sorry
