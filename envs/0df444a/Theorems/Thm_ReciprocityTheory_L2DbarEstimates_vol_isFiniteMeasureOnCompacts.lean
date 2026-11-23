-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_isFiniteMeasureOnCompacts
-- name    : ReciprocityTheory.L2DbarEstimates.vol_isFiniteMeasureOnCompacts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:11.003923+00:00
-- url     : https://prove2.me/theorems/5d352713-07f1-4ad3-9556-24f36257486e
-- title:
--   L2 Dbar Estimates: vol is Finite Measure On Compacts
-- statement:
--   The L2 Dbar Estimates construction uses the vol is Finite Measure On Compacts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L220-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/MeasurableSetImageOfIsLocalHomeomorph.lean#L220-L240

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

theorem ReciprocityTheory.L2DbarEstimates.vol_isFiniteMeasureOnCompacts {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) :
    IsFiniteMeasureOnCompacts (vol n z) := by sorry
