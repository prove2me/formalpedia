-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ck_prodFin_iff
-- name    : ReciprocityTheory.L2DbarEstimates.ck_prodFin_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:25.137525+00:00
-- url     : https://prove2.me/theorems/4437ef35-7e09-4be2-9faa-0217a867df27
-- title:
--   L2 Dbar Estimates: ck prod Fin iff
-- statement:
--   The L2 Dbar Estimates construction uses the ck prod Fin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L83-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L83-L92

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

theorem ReciprocityTheory.L2DbarEstimates.ck_prodFin_iff {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p k : ℕ) (F : M × Fin p → ℂ) :
    Ck n (fun q : M × Fin p => z q.1) k F ↔ ∀ i, Ck n z k (fun x => F (x, i)) := by sorry
