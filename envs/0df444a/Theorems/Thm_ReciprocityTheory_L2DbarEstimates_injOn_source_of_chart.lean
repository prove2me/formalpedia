-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_injOn_source_of_chart
-- name    : ReciprocityTheory.L2DbarEstimates.injOn_source_of_chart
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:00.1789+00:00
-- url     : https://prove2.me/theorems/5c44403d-c3c5-4b6f-a507-eb0fd453697c
-- title:
--   L2 Dbar Estimates: inj On source of chart
-- statement:
--   The L2 Dbar Estimates construction uses the inj On source of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L101-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L101-L104

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
omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

theorem ReciprocityTheory.L2DbarEstimates.injOn_source_of_chart (n : ℕ) (z : M → V n) (e : OpenPartialHomeomorph M (V n))
    (he : IsChart n z e) : InjOn z e.source := by sorry
