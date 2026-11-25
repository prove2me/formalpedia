-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_inner2
-- name    : ReciprocityTheory.L2DbarEstimates.F.splitT_inner2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:58:47.676404+00:00
-- url     : https://prove2.me/theorems/5d50229e-c9a7-4c88-b393-c3177b36a3ee
-- title:
--   F: split T inner2
-- statement:
--   The F construction uses the split T inner2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/SplitTest.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/SplitTest.lean#L87-L95

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_SplitTest
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
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}

theorem ReciprocityTheory.L2DbarEstimates.F.splitT_inner2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ph : M → ℝ) (hph : Continuous ph) (F G : M → E) (hF : MemLp F 2 (wvol n z ph))
    (hG : MemLp G 2 (wvol n z ph)) :
    ⟪hF.toLp F, hG.toLp G⟫_ℂ = ∫ x, ⟪F x, G x⟫_ℂ * (Real.exp (-ph x) : ℂ) ∂vol n z := by sorry
