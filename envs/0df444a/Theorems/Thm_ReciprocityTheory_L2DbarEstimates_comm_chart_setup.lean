-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_comm_chart_setup
-- name    : ReciprocityTheory.L2DbarEstimates.comm_chart_setup
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:07.747159+00:00
-- url     : https://prove2.me/theorems/9490a6ee-39e3-5cb6-9084-50a2bfce0b7d
-- title:
--   L2 Dbar Estimates: comm chart setup
-- statement:
--   The L2 Dbar Estimates construction uses the comm chart setup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L122-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/CommFderivApply.lean#L122-L141

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
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

theorem ReciprocityTheory.L2DbarEstimates.comm_chart_setup {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Ck n z 2 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M)
    (hx : x ∈ e.source) :
    z x ∈ e.target ∧ ContDiffAt ℝ 2 (f ∘ e.symm) (z x) ∧
      (∀ j, (d n z j f ∘ e.symm) =ᶠ[𝓝 (z x)] wd n j (f ∘ e.symm)) ∧
      (∀ j, (db n z j f ∘ e.symm) =ᶠ[𝓝 (z x)] wdb n j (f ∘ e.symm)) := by sorry
