-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_measurable_encard_fiber
-- name    : ReciprocityTheory.L2DbarEstimates.measurable_encard_fiber
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:11.665849+00:00
-- url     : https://prove2.me/theorems/a280a34c-3917-42a8-b98c-0cc3df783428
-- title:
--   L2 Dbar Estimates: measurable encard fiber
-- statement:
--   The L2 Dbar Estimates construction uses the measurable encard fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L111-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L111-L148

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

theorem ReciprocityTheory.L2DbarEstimates.measurable_encard_fiber (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (A : Set M)
    (hA : MeasurableSet A) :
    Measurable fun y => (((A ∩ z ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) := by sorry
