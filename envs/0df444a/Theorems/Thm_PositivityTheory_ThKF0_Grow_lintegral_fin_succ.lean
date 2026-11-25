-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Grow_lintegral_fin_succ
-- name    : PositivityTheory.ThKF0.Grow.lintegral_fin_succ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:51.465164+00:00
-- url     : https://prove2.me/theorems/fcfc5a24-5675-5deb-b87f-cb6af90aa839
-- title:
--   Grow: lintegral fin succ
-- statement:
--   The Grow construction uses the lintegral fin succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobA.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobA.lean#L40-L47

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Grow
open scoped ENNReal
open MeasureTheory

theorem PositivityTheory.ThKF0.Grow.lintegral_fin_succ {D : ℕ} (G : (Fin (D + 1) → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ t, G t = ∫⁻ s : ℝ, ∫⁻ t : Fin D → ℝ, G (Fin.cons s t) := by sorry
