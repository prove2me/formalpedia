-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_UMGS_hasFDerivAt_of_partials
-- name    : PositivityTheory.ThKEst.UMGS.hasFDerivAt_of_partials
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:26.430798+00:00
-- url     : https://prove2.me/theorems/02bebeb6-9d24-458a-92f9-bfb765ffbf7c
-- title:
--   UMGS: has FDeriv At of partials
-- statement:
--   The UMGS construction uses the has FDeriv At of partials property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L9-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/UMGSmoothA.lean#L9-L56

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_UMGSmoothA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.UMGS
open Filter Topology Function

theorem PositivityTheory.ThKEst.UMGS.hasFDerivAt_of_partials {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ) :
    ∀ (Φ : (Fin k → ℝ) → V) (D : Fin k → (Fin k → ℝ) → V), (∀ i, Continuous (D i)) →
      (∀ i t, HasDerivAt (fun s => Φ (update t i (t i + s))) (D i t) 0) →
      ∀ t, HasFDerivAt Φ (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D i t)) t := by sorry
