-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_apply
-- name    : ReciprocityTheory.L2DbarEstimates.vol_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:04.823473+00:00
-- url     : https://prove2.me/theorems/fde46599-fd7b-458c-b846-b515e5a5c437
-- title:
--   L2 Dbar Estimates: vol apply
-- statement:
--   The L2 Dbar Estimates construction uses the vol apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L170-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L170-L172

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

theorem ReciprocityTheory.L2DbarEstimates.vol_apply {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (A : Set M) (hA : MeasurableSet A) :
    vol n z A = volFun n z A := by sorry
