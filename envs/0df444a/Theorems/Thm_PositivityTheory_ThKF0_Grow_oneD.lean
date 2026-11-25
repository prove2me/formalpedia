-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Grow_oneD
-- name    : PositivityTheory.ThKF0.Grow.oneD
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:03:58.197652+00:00
-- url     : https://prove2.me/theorems/a6a7018f-7c5f-4fa1-8637-844933e20f90
-- title:
--   Grow: one D
-- statement:
--   The Grow construction uses the one D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobA.lean#L10-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobA.lean#L10-L38

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

theorem PositivityTheory.ThKF0.Grow.oneD (u u' : ℝ → ℂ) (hu' : Continuous u') (h : ∀ t, HasDerivAt u (u' t) t) :
    ‖u 0‖ₑ ^ 2 ≤ 2 * ∫⁻ t, (‖u t‖ₑ ^ 2 + ‖u' t‖ₑ ^ 2) := by sorry
