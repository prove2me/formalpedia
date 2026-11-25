-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_smooth_cutExt
-- name    : ReciprocityTheory.L2DbarEstimates.I.ap_smooth_cutExt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:58:37.930811+00:00
-- url     : https://prove2.me/theorems/0419c8b1-5d23-5f6f-bf77-8e075b7be7ec
-- title:
--   I: ap smooth cut Ext
-- statement:
--   The I construction uses the ap smooth cut Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L57-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L57-L74

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff Classical

theorem ReciprocityTheory.L2DbarEstimates.I.ap_smooth_cutExt {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ)
    (hph : SmoothR n z ph) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ) (ε : ℝ)
    (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) (hχs : ContDiff ℝ ∞ χ)
    (hχ0 : ∀ t, 1 ≤ t → χ t = 0) (hε : 0 < ε) (hm : ε ^ 2 < m) :
    Smooth n z (cutExt n z g ph r c W χ ε) := by sorry
