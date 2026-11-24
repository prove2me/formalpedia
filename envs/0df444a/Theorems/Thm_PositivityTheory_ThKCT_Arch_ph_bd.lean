-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_ph_bd
-- name    : PositivityTheory.ThKCT.Arch.ph_bd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:20.781364+00:00
-- url     : https://prove2.me/theorems/b0d5557f-e01e-4510-926d-b82033597fdc
-- title:
--   Arch: ph bd
-- statement:
--   The Arch construction uses the ph bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L143-L148

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

theorem PositivityTheory.ThKCT.Arch.ph_bd (l : V →L[ℝ] ℝ) (c : ℝ) (i : ℕ) (x : V) : ‖iteratedFDeriv ℝ i (ph l c) x‖ ≤ ‖l‖ ^ i := by sorry
