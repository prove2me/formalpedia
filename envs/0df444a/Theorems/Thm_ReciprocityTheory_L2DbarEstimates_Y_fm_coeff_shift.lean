-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fm_coeff_shift
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fm_coeff_shift
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:53.008919+00:00
-- url     : https://prove2.me/theorems/2405a265-d34d-5569-b231-e01932c49454
-- title:
--   Y: fm coeff shift
-- statement:
--   The Y construction uses the fm coeff shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourMul.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourMul.lean#L54-L61

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ComplexConjugate
noncomputable section
attribute [local instance] ReciprocityTheory.L2DbarEstimates.Y._p2m_local_instance_19aabe418c_38
attribute [local instance] ReciprocityTheory.L2DbarEstimates.Y._p2m_local_instance_19aabe418c_40

theorem ReciprocityTheory.L2DbarEstimates.Y.fm_coeff_shift {f : ℕ} (F : C(UnitAddTorus (Fin f), ℂ)) (ν i : Fin f → ℤ) :
    UnitAddTorus.mFourierCoeff (⇑(UnitAddTorus.mFourier (-ν) * F)) i =
      UnitAddTorus.mFourierCoeff (⇑F) (i + ν) := by sorry
