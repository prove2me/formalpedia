-- Prove2me | Theorems.Thm_PositivityTheory_ThKEst_LinDerPf_prod_strict
-- name    : PositivityTheory.ThKEst.LinDerPf.prod_strict
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:27.433806+00:00
-- url     : https://prove2.me/theorems/5b516ef2-e317-4388-829f-b887b95cd3a6
-- title:
--   Lin Der Pf: prod strict
-- statement:
--   The Lin Der Pf construction uses the prod strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L153-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/LinDerA.lean#L153-L169

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

theorem PositivityTheory.ThKEst.LinDerPf.prod_strict : ∀ (m : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (e : Fin m → V → A)
    (e' : Fin m → V →L[ℝ] A) (_ : ∀ i, HasStrictFDerivAt (e i) (e' i) 0) (_ : ∀ i, e i 0 = 1),
    HasStrictFDerivAt (fun s => (List.ofFn fun i => e i s).prod) (∑ i, e' i) 0 := by sorry
