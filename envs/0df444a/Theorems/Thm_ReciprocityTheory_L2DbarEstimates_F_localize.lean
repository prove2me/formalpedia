-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_localize
-- name    : ReciprocityTheory.L2DbarEstimates.F.localize
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:08:41.225375+00:00
-- url     : https://prove2.me/theorems/43bc31cb-8265-41b4-9697-a6c3d6b49672
-- title:
--   F: localize
-- statement:
--   The F construction uses the localize property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Localize.lean#L12-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/Localize.lean#L12-L127

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Localize
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

theorem ReciprocityTheory.L2DbarEstimates.F.localize (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hMD : MultDivStatement n M) (hMS : MultSStatement n M) :
    LocalizeStatement n M := by sorry
