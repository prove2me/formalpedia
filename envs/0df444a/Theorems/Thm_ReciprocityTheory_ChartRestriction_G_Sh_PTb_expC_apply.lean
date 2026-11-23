-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_expC_apply
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTb.expC_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:37:17.915807+00:00
-- url     : https://prove2.me/theorems/d5ef7ab5-a42c-40cc-bac7-41c08e34b376
-- title:
--   PTb: exp C apply
-- statement:
--   The PTb construction uses the exp C apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L198-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/CardToMultisetEqDegree.lean#L198-L203

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTb.expC_apply {q : ℕ} (hq : q ≠ 0) (ga : Fin d → PowerSeries C) (a : Fin d) :
    expC q ga a = PowerSeries.expand q hq (ga a) := by sorry
