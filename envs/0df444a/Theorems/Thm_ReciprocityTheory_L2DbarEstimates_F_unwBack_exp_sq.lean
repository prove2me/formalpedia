-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_unwBack_exp_sq
-- name    : ReciprocityTheory.L2DbarEstimates.F.unwBack_exp_sq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:49.85664+00:00
-- url     : https://prove2.me/theorems/ed7be374-93e0-5f53-938d-b50948d574e7
-- title:
--   F: unw Back exp sq
-- statement:
--   The F construction uses the unw Back exp sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightBackA.lean#L75-L77

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.F.unwBack_exp_sq (a : ℝ) : Real.exp a ^ 2 * Real.exp (-a) = Real.exp a := by sorry
