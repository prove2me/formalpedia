-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_smoothR_firstWeight
-- name    : ReciprocityTheory.L2DbarEstimates.F.smoothR_firstWeight
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:40.265318+00:00
-- url     : https://prove2.me/theorems/ccc651b7-aee2-5b6f-887f-5cb8f4155c9d
-- title:
--   F: smooth R first Weight
-- statement:
--   The F construction uses the smooth R first Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L73-L78

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
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

theorem ReciprocityTheory.L2DbarEstimates.F.smoothR_firstWeight (ph ψ : M → ℝ) (hph : SmoothR n z ph) (hψ : SmoothR n z ψ) :
    SmoothR n z (w1 ph ψ) := by sorry
