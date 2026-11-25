-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fm_conv
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fm_conv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:30.075028+00:00
-- url     : https://prove2.me/theorems/cc3fedc8-cf3c-411c-822d-971b755bf304
-- title:
--   Y: fm conv
-- statement:
--   The Y construction uses the fm conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourMul.lean#L63-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourMul.lean#L63-L85

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

theorem ReciprocityTheory.L2DbarEstimates.Y.fm_conv {f : ℕ} (F1 F2 : C(UnitAddTorus (Fin f), ℂ)) (ν : Fin f → ℤ) :
    HasSum (fun ν' => UnitAddTorus.mFourierCoeff (⇑F1) ν' * UnitAddTorus.mFourierCoeff (⇑F2) (ν - ν'))
      (UnitAddTorus.mFourierCoeff (⇑F1 * ⇑F2) ν) := by sorry
