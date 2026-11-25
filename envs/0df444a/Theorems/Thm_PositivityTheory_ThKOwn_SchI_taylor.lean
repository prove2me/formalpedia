-- Prove2me | Theorems.Thm_PositivityTheory_ThKOwn_SchI_taylor
-- name    : PositivityTheory.ThKOwn.SchI.taylor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:23.325855+00:00
-- url     : https://prove2.me/theorems/4eb19355-aba5-48ae-9ec1-15222cb5ab54
-- title:
--   Sch I: taylor
-- statement:
--   The Sch I construction uses the taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/JetApply.lean#L101-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/JetApply.lean#L101-L107

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

theorem PositivityTheory.ThKOwn.SchI.taylor : HasFTaylorSeriesUpTo ∞ (fun x => ∫ a, G a x ∂μ) fun x j => ∫ a, iteratedFDeriv ℝ j (G a) x ∂μ := by sorry
