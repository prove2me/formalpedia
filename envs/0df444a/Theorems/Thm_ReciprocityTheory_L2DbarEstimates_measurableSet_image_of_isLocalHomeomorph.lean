-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_measurableSet_image_of_isLocalHomeomorph
-- name    : ReciprocityTheory.L2DbarEstimates.measurableSet_image_of_isLocalHomeomorph
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:22:13.961737+00:00
-- url     : https://prove2.me/theorems/90bd33e8-bbeb-4804-8e90-d45a52198737
-- title:
--   L2 Dbar Estimates: measurable Set image of is Local Homeomorph
-- statement:
--   The L2 Dbar Estimates construction uses the measurable Set image of is Local Homeomorph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L58-L67

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M]

theorem ReciprocityTheory.L2DbarEstimates.measurableSet_image_of_isLocalHomeomorph (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z)
    (A : Set M) (hA : MeasurableSet A) : MeasurableSet (z '' A) := by sorry
