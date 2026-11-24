-- Prove2me | Theorems.Thm_PositivityTheory_ThKOwn_SchI_cont_D
-- name    : PositivityTheory.ThKOwn.SchI.cont_D
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:36.135858+00:00
-- url     : https://prove2.me/theorems/1d750266-da4d-492c-a6dd-d44efe9a4663
-- title:
--   Sch I: cont D
-- statement:
--   The Sch I construction uses the cont D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/JetApply.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/JetApply.lean#L58-L63

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
omit hI

theorem PositivityTheory.ThKOwn.SchI.cont_D (j : ℕ) (x : V) : Continuous fun a => iteratedFDeriv ℝ j (G a) x := by sorry
