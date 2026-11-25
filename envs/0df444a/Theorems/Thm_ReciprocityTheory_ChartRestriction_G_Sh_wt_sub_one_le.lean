-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_wt_sub_one_le
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.wt_sub_one_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:05.625431+00:00
-- url     : https://prove2.me/theorems/7ae22efc-9397-49ca-9fbe-e81466c0c2f2
-- title:
--   Sh: wt sub one le
-- statement:
--   The Sh construction uses the wt sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/WtSubOneLe.lean#L78-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/WtSubOneLe.lean#L78-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TypicalCurveStructureConstants
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CoeffLgPcurveTop
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_GeomSumRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_WtSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh.PTb
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.Sh.wt_sub_one_le {r : ℝ} {y : WithTop ℝ} (h : (r : WithTop ℝ) ≤ 1 + y) :
    ((r - 1 : ℝ) : WithTop ℝ) ≤ y := by sorry
