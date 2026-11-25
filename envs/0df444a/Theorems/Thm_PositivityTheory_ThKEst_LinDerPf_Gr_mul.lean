-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_Gr_mul
-- name    : PositivityTheory.ThKEst.LinDerPf.Gr.mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:25.73495+00:00
-- url     : https://prove2.me/theorems/68dd74df-1f86-491d-b764-c430946d274b
-- title:
--   Gr: mul
-- statement:
--   The Gr construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L109-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L109-L112

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_LinDerA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.LinDerPf
open Filter Topology Asymptotics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
variable {a : A →L[ℝ] A}

theorem PositivityTheory.ThKEst.LinDerPf.Gr.mul (ha : ∀ x y, a (x * y) = a y * a x) {g h : A} (hg : Gr a g) (hh : Gr a h) : Gr a (g * h) := by sorry
