-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_hormander
-- name    : ReciprocityTheory.L2DbarEstimates.F.hormander
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:42:06.019951+00:00
-- url     : https://prove2.me/theorems/b5a169e2-03f0-443c-b1aa-99b6551c0804
-- title:
--   F: hormander
-- statement:
--   The F construction uses the hormander property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/Hormander.lean#L13-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/HormanderEstimate/Hormander.lean#L13-L107

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_GmSingleIsTestForm
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_HormanderEstimate_Hormander
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

theorem ReciprocityTheory.L2DbarEstimates.F.hormander (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hTI : TestIneqStatement n M) (hReg : RegMStatement n M) :
    HStatement n M := by sorry
