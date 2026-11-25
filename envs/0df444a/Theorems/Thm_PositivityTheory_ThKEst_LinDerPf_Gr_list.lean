-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_Gr_list
-- name    : PositivityTheory.ThKEst.LinDerPf.Gr.list
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:11.477079+00:00
-- url     : https://prove2.me/theorems/54154ba4-950a-44a7-9023-756ce4b7231e
-- title:
--   Gr: list
-- statement:
--   The Gr construction uses the list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L114-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L114-L120

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

theorem PositivityTheory.ThKEst.LinDerPf.Gr.list (ha : ∀ x y, a (x * y) = a y * a x) (h1 : a 1 = 1) (l : List A) (hl : ∀ g ∈ l, Gr a g) :
    Gr a l.prod := by sorry
