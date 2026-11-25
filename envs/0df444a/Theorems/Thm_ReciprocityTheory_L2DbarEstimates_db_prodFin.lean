-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_prodFin
-- name    : ReciprocityTheory.L2DbarEstimates.db_prodFin
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:01:49.724211+00:00
-- url     : https://prove2.me/theorems/615fd09b-71c8-5fcd-99c1-4afa0c8e90dd
-- title:
--   L2 Dbar Estimates: db prod Fin
-- statement:
--   The L2 Dbar Estimates construction uses the db prod Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L112-L117

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IsLocalHomeomorphCompFst
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

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

theorem ReciprocityTheory.L2DbarEstimates.db_prodFin {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (j : Fin n) (F : M × Fin p → ℂ) (x : M) (i : Fin p) :
    db n (fun q : M × Fin p => z q.1) j F (x, i) = db n z j (fun y => F (y, i)) x := by sorry
