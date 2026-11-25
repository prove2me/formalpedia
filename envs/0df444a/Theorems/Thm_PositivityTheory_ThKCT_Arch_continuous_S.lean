-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_continuous_S
-- name    : PositivityTheory.ThKCT.Arch.continuous_S
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:57:46.556644+00:00
-- url     : https://prove2.me/theorems/0f02584e-fa2e-5b40-bf6d-369afe309bab
-- title:
--   Arch: continuous S
-- statement:
--   The Arch construction uses the continuous S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L250-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L250-L259

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

theorem PositivityTheory.ThKCT.Arch.continuous_S (f : SchwartzMap V ℂ) : Continuous fun w => S w f := by sorry
