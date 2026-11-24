-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_u_smooth
-- name    : PositivityTheory.ThKCT.Arch.u_smooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:10.686516+00:00
-- url     : https://prove2.me/theorems/4ce6fe64-bd94-4d59-aec5-d67bf1d585eb
-- title:
--   Arch: u smooth
-- statement:
--   The Arch construction uses the u smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L127-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L127-L128

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

theorem PositivityTheory.ThKCT.Arch.u_smooth (c : ℝ) : ContDiff ℝ ∞ fun s : ℝ => cexp (I * ((s + c : ℝ) : ℂ)) := by sorry
