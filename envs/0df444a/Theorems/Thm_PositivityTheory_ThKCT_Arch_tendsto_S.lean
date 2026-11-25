-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_tendsto_S
-- name    : PositivityTheory.ThKCT.Arch.tendsto_S
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:27.493077+00:00
-- url     : https://prove2.me/theorems/1f179af4-fa5d-4bb9-9814-f0c2a7a2effe
-- title:
--   Arch: tendsto S
-- statement:
--   The Arch construction uses the tendsto S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L241-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L241-L248

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

theorem PositivityTheory.ThKCT.Arch.tendsto_S (f : SchwartzMap V ℂ) : Tendsto (fun w => S w f) (𝓝 0) (𝓝 f) := by sorry
