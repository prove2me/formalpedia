-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_lip
-- name    : PositivityTheory.ThKCT.Arch.lip
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:59.950368+00:00
-- url     : https://prove2.me/theorems/b1e2b499-16d6-4eb4-9e72-35c60f9d485b
-- title:
--   Arch: lip
-- statement:
--   The Arch construction uses the lip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L196-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L196-L220

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

theorem PositivityTheory.ThKCT.Arch.lip (q : Seminorm ℂ (SchwartzMap V ℂ)) (hq : Continuous q) : ∃ p : Seminorm ℂ (SchwartzMap V ℂ),
    Continuous p ∧ ∀ w f, ‖w‖ ≤ 1 → q (S w f - f) ≤ ‖w‖ * p f := by sorry
