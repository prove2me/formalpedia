-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_lip_pow
-- name    : PositivityTheory.ThKCT.Arch.lip_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:09.546439+00:00
-- url     : https://prove2.me/theorems/7ef57ead-6262-54ed-a860-5575a9b427ea
-- title:
--   Arch: lip pow
-- statement:
--   The Arch construction uses the lip pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L261-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L261-L271

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

theorem PositivityTheory.ThKCT.Arch.lip_pow (n : ℕ) : ∀ q : Seminorm ℂ (SchwartzMap V ℂ), Continuous q → ∃ p : Seminorm ℂ (SchwartzMap V ℂ),
    Continuous p ∧ ∀ w f, ‖w‖ ≤ 1 → q ((fun g => S w g - g)^[n] f) ≤ ‖w‖ ^ n * p f := by sorry
