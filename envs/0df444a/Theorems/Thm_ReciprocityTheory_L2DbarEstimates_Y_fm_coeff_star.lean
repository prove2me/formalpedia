-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_fm_coeff_star
-- name    : ReciprocityTheory.L2DbarEstimates.Y.fm_coeff_star
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:00:23.936559+00:00
-- url     : https://prove2.me/theorems/97c59dda-82c6-4f09-8535-b1a3798bb3bb
-- title:
--   Y: fm coeff star
-- statement:
--   The Y construction uses the fm coeff star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourMul.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourMul.lean#L46-L52

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

theorem ReciprocityTheory.L2DbarEstimates.Y.fm_coeff_star {f : ℕ} (F : C(UnitAddTorus (Fin f), ℂ)) (i : Fin f → ℤ) :
    conj (UnitAddTorus.mFourierCoeff (⇑(star F)) i) = UnitAddTorus.mFourierCoeff (⇑F) (-i) := by sorry
