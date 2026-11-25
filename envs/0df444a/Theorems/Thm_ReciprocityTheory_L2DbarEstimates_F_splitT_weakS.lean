-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_weakS
-- name    : ReciprocityTheory.L2DbarEstimates.F.splitT_weakS
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:57:40.477572+00:00
-- url     : https://prove2.me/theorems/7db45ea2-b73a-46df-9654-1bec56299a9a
-- title:
--   F: split T weak S
-- statement:
--   The F construction uses the split T weak S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/SplitTest.lean#L108-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/SplitTest.lean#L108-L115

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

theorem ReciprocityTheory.L2DbarEstimates.F.splitT_weakS (F G : M → V n) (hFG : F =ᵐ[vol n z] G) (σ : M → Fin n → Fin n → ℂ)
    (h : IsWeakS n z F σ) : IsWeakS n z G σ := by sorry
