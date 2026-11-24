-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_nonneg
-- name    : PositivityTheory.ThKCT.Arch.Bd.nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:01:00.739895+00:00
-- url     : https://prove2.me/theorems/fb5444ce-71b4-4309-b30a-d11b91526877
-- title:
--   Bd: nonneg
-- statement:
--   The Bd construction uses the nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L33-L34

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

theorem PositivityTheory.ThKCT.Arch.Bd.nonneg {m : ℕ} {f : V → ℂ} {C : ℝ} (h : Bd m f C) : 0 ≤ C := by sorry
