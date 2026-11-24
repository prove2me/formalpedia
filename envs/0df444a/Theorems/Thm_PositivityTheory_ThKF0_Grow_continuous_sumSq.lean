-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Grow_continuous_sumSq
-- name    : PositivityTheory.ThKF0.Grow.continuous_sumSq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:34:16.262886+00:00
-- url     : https://prove2.me/theorems/7563e326-f518-47e9-8fc9-9316496598a0
-- title:
--   Grow: continuous sum Sq
-- statement:
--   The Grow construction uses the continuous sum Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobA.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobA.lean#L62-L64

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Grow
open scoped ENNReal
open MeasureTheory
variable {X W : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
omit [AddCommGroup X] [IsTopologicalAddGroup X]

theorem PositivityTheory.ThKF0.Grow.continuous_sumSq {S : Set (X → ℂ)} (hS : ∀ Θ ∈ S, Continuous Θ) {dd : W → (X → ℂ) → X → ℂ}
    (hd : ∀ w, ∀ Θ ∈ S, dd w Θ ∈ S) (L : List (List W)) {Θ : X → ℂ} (h : Θ ∈ S) : Continuous (sumSq dd L Θ) := by sorry
