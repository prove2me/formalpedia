-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Grow_lintegral_sumSq
-- name    : PositivityTheory.ThKF0.Grow.lintegral_sumSq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:03:55.069017+00:00
-- url     : https://prove2.me/theorems/78b52449-07c0-5dbf-a80b-8428faa74d22
-- title:
--   Grow: lintegral sum Sq
-- statement:
--   The Grow construction uses the lintegral sum Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobA.lean#L111-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobA.lean#L111-L119

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

theorem PositivityTheory.ThKF0.Grow.lintegral_sumSq [MeasurableSpace X] [BorelSpace X] (μ : Measure X) {S : Set (X → ℂ)} (hS : ∀ Θ ∈ S, Continuous Θ)
    {dd : W → (X → ℂ) → X → ℂ} (hd : ∀ w, ∀ Θ ∈ S, dd w Θ ∈ S) (L : List (List W)) {Θ : X → ℂ} (h : Θ ∈ S) :
    ∫⁻ y, sumSq dd L Θ y ∂μ = (L.map fun l => ∫⁻ y, ‖l.foldr dd Θ y‖ₑ ^ 2 ∂μ).sum := by sorry
