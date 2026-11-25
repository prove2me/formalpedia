-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_holo_prodFin_iff
-- name    : ReciprocityTheory.L2DbarEstimates.holo_prodFin_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:01:55.484441+00:00
-- url     : https://prove2.me/theorems/c3a0c2a8-df9f-448f-bded-937c9ff24879
-- title:
--   L2 Dbar Estimates: holo prod Fin iff
-- statement:
--   The L2 Dbar Estimates construction uses the holo prod Fin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L94-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IsLocalHomeomorphCompFst.lean#L94-L103

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

theorem ReciprocityTheory.L2DbarEstimates.holo_prodFin_iff {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (F : M × Fin p → ℂ) :
    Holo n (fun q : M × Fin p => z q.1) F ↔ ∀ i, Holo n z (fun x => F (x, i)) := by sorry
