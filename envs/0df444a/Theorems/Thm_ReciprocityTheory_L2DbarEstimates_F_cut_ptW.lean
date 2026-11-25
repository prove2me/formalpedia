-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_ptW
-- name    : ReciprocityTheory.L2DbarEstimates.F.cut_ptW
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:55:51.410631+00:00
-- url     : https://prove2.me/theorems/cb55baf2-e7f5-5989-b53e-1fffc0ad2b49
-- title:
--   F: cut pt W
-- statement:
--   The F construction uses the cut pt W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L265-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L265-L294

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

theorem ReciprocityTheory.L2DbarEstimates.F.cut_ptW (c : ℝ) (hc : |c| ≤ 1) (wx S : ℂ) (fx2 D ph ψ : ℝ) (hS : ‖S‖ ^ 2 ≤ D * fx2)
    (hD : D ≤ Real.exp ψ) (hf2 : 0 ≤ fx2) :
    ‖(c : ℂ) * wx - (Real.exp (-ψ) : ℂ) * S‖ ^ 2 * Real.exp (-(ph - 2 * ψ)) ≤
      2 * (‖wx‖ ^ 2 * Real.exp (-(ph - 2 * ψ))) + 2 * (fx2 * Real.exp (-(ph - ψ))) := by sorry
