-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_cut_ptS
-- name    : ReciprocityTheory.L2DbarEstimates.F.cut_ptS
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:56:44.66301+00:00
-- url     : https://prove2.me/theorems/3533aae9-92a9-4757-a468-7ee6fa9bfc6c
-- title:
--   F: cut pt S
-- statement:
--   The F construction uses the cut pt S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L296-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/CutoffA.lean#L296-L325

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

theorem ReciprocityTheory.L2DbarEstimates.F.cut_ptS {n : ℕ} (c : ℝ) (hc : |c| ≤ 1) (σx : Fin n → Fin n → ℂ) (a b : Fin n → ℂ)
    (D fx2 ph ψ : ℝ) (ha : ∑ i, ‖a i‖ ^ 2 = D) (hb : ∑ i, ‖b i‖ ^ 2 = fx2)
    (hD : D ≤ Real.exp ψ) :
    sq2 n (fun j k => (c : ℂ) * σx j k + wedge a b j k) * Real.exp (-ph) ≤
      2 * (sq2 n σx * Real.exp (-ph)) + 4 * (fx2 * Real.exp (-(ph - ψ))) := by sorry
