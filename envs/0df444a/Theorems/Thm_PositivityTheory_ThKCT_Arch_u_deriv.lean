-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_u_deriv
-- name    : PositivityTheory.ThKCT.Arch.u_deriv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:24.34597+00:00
-- url     : https://prove2.me/theorems/be75e188-5557-4dc9-b963-84d7b4e0ab92
-- title:
--   Arch: u deriv
-- statement:
--   The Arch construction uses the u deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L132-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L132-L141

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

theorem PositivityTheory.ThKCT.Arch.u_deriv (c : ℝ) (i : ℕ) :
    iteratedDeriv i (fun s : ℝ => cexp (I * ((s + c : ℝ) : ℂ))) = fun s : ℝ => I ^ i * cexp (I * ((s + c : ℝ) : ℂ)) := by sorry
