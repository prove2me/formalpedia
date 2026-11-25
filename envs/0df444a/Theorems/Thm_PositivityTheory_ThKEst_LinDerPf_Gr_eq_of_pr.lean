-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_Gr_eq_of_pr
-- name    : PositivityTheory.ThKEst.LinDerPf.Gr.eq_of_pr
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:22.067642+00:00
-- url     : https://prove2.me/theorems/564ea8e5-96f7-420a-a53d-0243e4830640
-- title:
--   Gr: eq of pr
-- statement:
--   The Gr construction uses the eq of pr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L130-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L130-L151

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

theorem PositivityTheory.ThKEst.LinDerPf.Gr.eq_of_pr {g h : A} (hg : Gr a g) (hh : Gr a h) (h1 : ‖1 - a g‖ ≤ 1 / 2) (h2 : ‖1 - a h‖ ≤ 1 / 2)
    (e : pr a g = pr a h) : g = h := by sorry
