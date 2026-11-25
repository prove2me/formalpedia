-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_grow
-- name    : PositivityTheory.ThKCT.Arch.grow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:58:51.676502+00:00
-- url     : https://prove2.me/theorems/7990c0d5-4716-4bed-ad27-2a1625d955ba
-- title:
--   Arch: grow
-- statement:
--   The Arch construction uses the grow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L178-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L178-L194

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

theorem PositivityTheory.ThKCT.Arch.grow (q : Seminorm ℂ (SchwartzMap V ℂ)) (hq : Continuous q) : ∃ (p : Seminorm ℂ (SchwartzMap V ℂ)) (M : ℕ),
    Continuous p ∧ ∀ w f, q (S w f) ≤ (1 + ‖w‖) ^ M * p f := by sorry
