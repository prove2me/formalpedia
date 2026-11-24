-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_pr_apply
-- name    : PositivityTheory.ThKEst.LinDerPf.pr_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:35.5977+00:00
-- url     : https://prove2.me/theorems/364d2689-875e-408d-91dc-e1cbd4722211
-- title:
--   Lin Der Pf: pr apply
-- statement:
--   The Lin Der Pf construction uses the pr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L105-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L105-L105

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

theorem PositivityTheory.ThKEst.LinDerPf.pr_apply (a : A →L[ℝ] A) (x : A) : pr a x = (1 / 2 : ℝ) • (x - a x) := by sorry
