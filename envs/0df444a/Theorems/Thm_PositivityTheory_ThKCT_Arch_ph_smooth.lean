-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_ph_smooth
-- name    : PositivityTheory.ThKCT.Arch.ph_smooth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:43.753267+00:00
-- url     : https://prove2.me/theorems/39a3bd0e-c576-4f5c-a600-6e628f79d849
-- title:
--   Arch: ph smooth
-- statement:
--   The Arch construction uses the ph smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L130-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L130-L130

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

theorem PositivityTheory.ThKCT.Arch.ph_smooth (l : V →L[ℝ] ℝ) (c : ℝ) : ContDiff ℝ ∞ (ph l c) := by sorry
