-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_ph_temp
-- name    : PositivityTheory.ThKCT.Arch.ph_temp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:28.39628+00:00
-- url     : https://prove2.me/theorems/25551389-4154-4806-9020-88ff0576e2a7
-- title:
--   Arch: ph temp
-- statement:
--   The Arch construction uses the ph temp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L150-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L150-L151

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

theorem PositivityTheory.ThKCT.Arch.ph_temp (l : V →L[ℝ] ℝ) (c : ℝ) : (ph l c).HasTemperateGrowth := by sorry
