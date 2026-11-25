-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_unweightRel
-- name    : ReciprocityTheory.L2DbarEstimates.F.unweightRel
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:57:20.27682+00:00
-- url     : https://prove2.me/theorems/972eb502-de9e-59d6-ba79-958e881cf8e2
-- title:
--   F: unweight Rel
-- statement:
--   The F construction uses the unweight Rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L181-L345
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/UnweightRel.lean#L181-L345

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

theorem ReciprocityTheory.L2DbarEstimates.F.unweightRel (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : UnweightRelStatement n M := by sorry
