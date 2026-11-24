-- Prove2me | Theorems.Thm_PositivityTheory_ThKOwn_SchI_J_apply
-- name    : PositivityTheory.ThKOwn.SchI.J_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:25.003682+00:00
-- url     : https://prove2.me/theorems/280d7db7-30b1-48dc-a07e-ab24bb4f6f3e
-- title:
--   Sch I: J apply
-- statement:
--   The Sch I construction uses the J apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/JetApply.lean#L45-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SchwartzMoments/JetApply.lean#L45-L45

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

theorem PositivityTheory.ThKOwn.SchI.J_apply (k j : ℕ) (f : SchwartzMap V ℂ) : J k j f = jet k j f := by sorry
