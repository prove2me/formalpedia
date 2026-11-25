-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_shift_sub
-- name    : PositivityTheory.ThKCT.Arch.Bd.shift_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:11.476373+00:00
-- url     : https://prove2.me/theorems/d2b7bf9e-1df1-465a-9712-253415b7a5c7
-- title:
--   Bd: shift sub
-- statement:
--   The Bd construction uses the shift sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L71-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L71-L91

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem PositivityTheory.ThKCT.Arch.Bd.shift_sub {m : ℕ} {f : V → ℂ} (hf : ContDiff ℝ ∞ f) {C : ℝ} (h : Bd (m + 1) f C) (t : V) :
    Bd m (fun x => f (x + t) - f x) ((1 + ‖t‖) ^ m * C * ‖t‖) := by sorry
