-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_ph_sub_bd
-- name    : PositivityTheory.ThKCT.Arch.ph_sub_bd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:16.619811+00:00
-- url     : https://prove2.me/theorems/10669c7a-b961-5fca-ac7d-bdd3d635f8a1
-- title:
--   Arch: ph sub bd
-- statement:
--   The Arch construction uses the ph sub bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L153-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L153-L166

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

theorem PositivityTheory.ThKCT.Arch.ph_sub_bd (l : V →L[ℝ] ℝ) (c : ℝ) {δ : ℝ} (h1 : δ ≤ 1) (hl : ‖l‖ ≤ δ) (hc : |c| ≤ δ) (i : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ i (fun x => ph l c x - 1) x‖ ≤ δ * (1 + ‖x‖) ^ 1 := by sorry
