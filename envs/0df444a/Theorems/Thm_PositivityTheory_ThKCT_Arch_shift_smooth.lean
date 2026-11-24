-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_shift_smooth
-- name    : PositivityTheory.ThKCT.Arch.shift_smooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:01.613068+00:00
-- url     : https://prove2.me/theorems/23b18b60-4619-48b8-98d9-5e9d15008d57
-- title:
--   Arch: shift smooth
-- statement:
--   The Arch construction uses the shift smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L175-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L175-L176

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

theorem PositivityTheory.ThKCT.Arch.shift_smooth (f : SchwartzMap V ℂ) (t : V) : ContDiff ℝ ∞ fun x => f (x + t) := by sorry
