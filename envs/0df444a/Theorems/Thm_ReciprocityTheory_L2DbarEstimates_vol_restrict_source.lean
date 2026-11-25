-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_restrict_source
-- name    : ReciprocityTheory.L2DbarEstimates.vol_restrict_source
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:17.228797+00:00
-- url     : https://prove2.me/theorems/42794893-331f-401b-91a3-6b2403f73073
-- title:
--   L2 Dbar Estimates: vol restrict source
-- statement:
--   The L2 Dbar Estimates construction uses the vol restrict source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L181-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L181-L193

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

theorem ReciprocityTheory.L2DbarEstimates.vol_restrict_source {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) :
    (vol n z).restrict e.source = Measure.map e.symm (volume.restrict e.target) := by sorry
