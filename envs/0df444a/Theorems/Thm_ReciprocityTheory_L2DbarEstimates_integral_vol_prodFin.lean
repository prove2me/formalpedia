-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_vol_prodFin
-- name    : ReciprocityTheory.L2DbarEstimates.integral_vol_prodFin
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:36:51.552551+00:00
-- url     : https://prove2.me/theorems/254ebaa6-6240-4d52-9465-a60e0cdf2507
-- title:
--   L2 Dbar Estimates: integral vol prod Fin
-- statement:
--   The L2 Dbar Estimates construction uses the integral vol prod Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L165-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L165-L171

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

theorem ReciprocityTheory.L2DbarEstimates.integral_vol_prodFin {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (f : M × Fin p → ℂ) (hf : Integrable f (vol n (fun q : M × Fin p => z q.1))) :
    ∫ q, f q ∂vol n (fun q : M × Fin p => z q.1) = ∑ i, ∫ x, f (x, i) ∂vol n z := by sorry
