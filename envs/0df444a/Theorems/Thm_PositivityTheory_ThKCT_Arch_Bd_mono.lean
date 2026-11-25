-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_mono
-- name    : PositivityTheory.ThKCT.Arch.Bd.mono
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:57:17.150362+00:00
-- url     : https://prove2.me/theorems/22fcb0cd-44e7-48fe-bb6f-d06420301952
-- title:
--   Bd: mono
-- statement:
--   The Bd construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L36-L37

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

theorem PositivityTheory.ThKCT.Arch.Bd.mono {m : ℕ} {f : V → ℂ} {C C' : ℝ} (h : Bd m f C) (hC : C ≤ C') : Bd m f C' := by sorry
