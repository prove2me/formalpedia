-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_prodFin
-- name    : ReciprocityTheory.L2DbarEstimates.d_prodFin
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:35.163154+00:00
-- url     : https://prove2.me/theorems/c413e349-8f3c-4df2-b80f-3ccfc5d62250
-- title:
--   L2 Dbar Estimates: d prod Fin
-- statement:
--   The L2 Dbar Estimates construction uses the d prod Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L105-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L105-L110

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IsLocalHomeomorphCompFst
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

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

theorem ReciprocityTheory.L2DbarEstimates.d_prodFin {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (j : Fin n) (F : M × Fin p → ℂ) (x : M) (i : Fin p) :
    d n (fun q : M × Fin p => z q.1) j F (x, i) = d n z j (fun y => F (y, i)) x := by sorry
