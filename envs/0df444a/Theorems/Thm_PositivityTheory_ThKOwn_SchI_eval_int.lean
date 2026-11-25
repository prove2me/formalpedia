-- Prove2me | Theorems.Thm_PositivityTheory_ThKOwn_SchI_eval_int
-- name    : PositivityTheory.ThKOwn.SchI.eval_int
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:04:47.665803+00:00
-- url     : https://prove2.me/theorems/a2b63188-894d-5d61-83b0-d0bcaf85c4d8
-- title:
--   Sch I: eval int
-- statement:
--   The Sch I construction uses the eval int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/JetApply.lean#L109-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/JetApply.lean#L109-L115

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SchwartzMoments_JetApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKOwn
open PositivityTheory.ThKOwn.SchI
open scoped ContDiff NNReal BoundedContinuousFunction
open MeasureTheory Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {α : Type} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
  {G : α → SchwartzMap V ℂ} (hG : Continuous G) (hI : ∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ)
include hG hI

theorem PositivityTheory.ThKOwn.SchI.eval_int (k j : ℕ) (x : V) :
    (∫ a, J k j (G a) ∂μ) x = ‖x‖ ^ k • iteratedFDeriv ℝ j (fun x => ∫ a, G a x ∂μ) x := by sorry
