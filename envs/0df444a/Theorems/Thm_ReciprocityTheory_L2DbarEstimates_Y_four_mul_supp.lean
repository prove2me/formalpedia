-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_four_mul_supp
-- name    : ReciprocityTheory.L2DbarEstimates.Y.four_mul_supp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:13.458001+00:00
-- url     : https://prove2.me/theorems/c07ec453-2088-489f-952c-2667cf8989d2
-- title:
--   Y: four mul supp
-- statement:
--   The Y construction uses the four mul supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourMul.lean#L166-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/FourMul.lean#L166-L178

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

theorem ReciprocityTheory.L2DbarEstimates.Y.four_mul_supp (f : ℕ) : FOURMulSuppStatement f := by sorry
