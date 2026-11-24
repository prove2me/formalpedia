-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_P_le
-- name    : PositivityTheory.ThKCT.Arch.P_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:01.338388+00:00
-- url     : https://prove2.me/theorems/eb4463d0-cdf9-41fd-90f8-4b255ac1598d
-- title:
--   Arch: P le
-- statement:
--   The Arch construction uses the P le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L43-L49

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

theorem PositivityTheory.ThKCT.Arch.P_le {m : ℕ} {f : SchwartzMap V ℂ} {C : ℝ} (h : Bd m f C) : P V m f ≤ C := by sorry
