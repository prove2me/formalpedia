-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_cs
-- name    : ReciprocityTheory.L2DbarEstimates.F.cut_cs
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:48.126858+00:00
-- url     : https://prove2.me/theorems/64ef9335-ad36-5dba-ad4f-c2ab1e320bd9
-- title:
--   F: cut cs
-- statement:
--   The F construction uses the cut cs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L70-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L70-L80

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA
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

theorem ReciprocityTheory.L2DbarEstimates.F.cut_cs (n : ℕ) (a b : Fin n → ℂ) :
    ‖∑ j, a j * b j‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * (∑ j, ‖b j‖ ^ 2) := by sorry
