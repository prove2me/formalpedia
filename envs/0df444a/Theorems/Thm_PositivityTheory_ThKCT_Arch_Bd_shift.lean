-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_shift
-- name    : PositivityTheory.ThKCT.Arch.Bd.shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:41.542788+00:00
-- url     : https://prove2.me/theorems/8349023f-998f-4a01-b6eb-9b8c1afd0427
-- title:
--   Bd: shift
-- statement:
--   The Bd construction uses the shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L63-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L63-L69

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

theorem PositivityTheory.ThKCT.Arch.Bd.shift {m : ℕ} {f : V → ℂ} {C : ℝ} (h : Bd m f C) (t : V) : Bd m (fun x => f (x + t)) ((1 + ‖t‖) ^ m * C) := by sorry
