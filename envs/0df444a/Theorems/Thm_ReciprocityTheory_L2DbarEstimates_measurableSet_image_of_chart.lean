-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_measurableSet_image_of_chart
-- name    : ReciprocityTheory.L2DbarEstimates.measurableSet_image_of_chart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:33:02.326917+00:00
-- url     : https://prove2.me/theorems/f154c9c5-7439-420d-99c2-3da71a59d2ff
-- title:
--   L2 Dbar Estimates: measurable Set image of chart
-- statement:
--   The L2 Dbar Estimates construction uses the measurable Set image of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L15-L28

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

theorem ReciprocityTheory.L2DbarEstimates.measurableSet_image_of_chart (n : ℕ) (z : M → V n) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) (S : Set M) (hS : MeasurableSet S) (hSe : S ⊆ e.source) :
    MeasurableSet (z '' S) := by sorry
