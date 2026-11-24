-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_add
-- name    : PositivityTheory.ThKCT.Arch.Bd.add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:08.62295+00:00
-- url     : https://prove2.me/theorems/634c4a62-503b-4e8e-9f52-f96ce0512d95
-- title:
--   Bd: add
-- statement:
--   The Bd construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L116-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L116-L123

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

theorem PositivityTheory.ThKCT.Arch.Bd.add {m : ℕ} {f g : V → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {C D : ℝ} (h : Bd m f C) (h' : Bd m g D) :
    Bd m (fun x => f x + g x) (C + D) := by sorry
