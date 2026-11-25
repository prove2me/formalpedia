-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_dbar_cutExt
-- name    : ReciprocityTheory.L2DbarEstimates.I.ap_dbar_cutExt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:57:48.218797+00:00
-- url     : https://prove2.me/theorems/5ddb1e5f-3d62-4514-9ef6-6844a4b851c0
-- title:
--   I: ap dbar cut Ext
-- statement:
--   The I construction uses the ap dbar cut Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L83-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyB.lean#L83-L110

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

theorem ReciprocityTheory.L2DbarEstimates.I.ap_dbar_cutExt {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (hg : ∀ i, Holo n z (g i)) (ph : M → ℝ)
    (hph : SmoothR n z ph) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ) (χ : ℝ → ℝ) (ε : ℝ)
    (hS : (zeroSet n g).Finite) (hW : IsLocalData n g ph r W m) (hχs : ContDiff ℝ ∞ χ)
    (x : M) (hx : ev n g ph r x < m) (ξ : Fin n → ℂ) :
    dbarDot n z (cutExt n z g ph r c W χ ε) x ξ =
      ((deriv χ (ev n g ph r x / ε ^ 2) * (1 / ε ^ 2) : ℝ) : ℂ) * gt n z g c W x *
        dbarDot n z (fun y => (ev n g ph r y : ℂ)) x ξ := by sorry
