-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_prodFin_eq
-- name    : ReciprocityTheory.L2DbarEstimates.vol_prodFin_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:31.310313+00:00
-- url     : https://prove2.me/theorems/3520841c-47f7-4bb7-97de-18c6c717df1f
-- title:
--   L2 Dbar Estimates: vol prod Fin eq
-- statement:
--   The L2 Dbar Estimates construction uses the vol prod Fin eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L141-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L141-L157

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IsLocalHomeomorphCompFst
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

theorem ReciprocityTheory.L2DbarEstimates.vol_prodFin_eq {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) :
    vol n (fun q : M × Fin p => z q.1) = ∑ i, (vol n z).map (fun x => (x, i)) := by sorry
