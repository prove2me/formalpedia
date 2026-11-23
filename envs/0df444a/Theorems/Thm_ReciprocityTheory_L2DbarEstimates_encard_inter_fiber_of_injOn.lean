-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_encard_inter_fiber_of_injOn
-- name    : ReciprocityTheory.L2DbarEstimates.encard_inter_fiber_of_injOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:31.721631+00:00
-- url     : https://prove2.me/theorems/9eb3725b-439d-4dd6-882b-54675ef9b299
-- title:
--   L2 Dbar Estimates: encard inter fiber of inj On
-- statement:
--   The L2 Dbar Estimates construction uses the encard inter fiber of inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L71-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L71-L90

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

theorem ReciprocityTheory.L2DbarEstimates.encard_inter_fiber_of_injOn (n : ℕ) (z : M → V n) (S : Set M) (hS : InjOn z S) (y : V n) :
    (((S ∩ z ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) = (z '' S).indicator 1 y := by sorry
