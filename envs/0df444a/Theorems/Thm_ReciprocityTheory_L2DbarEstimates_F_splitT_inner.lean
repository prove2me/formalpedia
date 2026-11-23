-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_inner
-- name    : ReciprocityTheory.L2DbarEstimates.F.splitT_inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:34.160014+00:00
-- url     : https://prove2.me/theorems/89af7d0e-6c82-42c2-95a5-a101a9adc9ab
-- title:
--   F: split T inner
-- statement:
--   The F construction uses the split T inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/SplitTest.lean#L71-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/SplitTest.lean#L71-L85

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

theorem ReciprocityTheory.L2DbarEstimates.F.splitT_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ph : M → ℝ) (hph : Continuous ph) (F : M → E) (hF : MemLp F 2 (wvol n z ph))
    (G : Lp E 2 (wvol n z ph)) :
    ⟪hF.toLp F, G⟫_ℂ = ∫ x, ⟪F x, G x⟫_ℂ * (Real.exp (-ph x) : ℂ) ∂vol n z := by sorry
