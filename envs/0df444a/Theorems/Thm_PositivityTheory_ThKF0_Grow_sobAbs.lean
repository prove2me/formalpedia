-- Prove2me | Theorems.Thm_PositivityTheory_ThKF0_Grow_sobAbs
-- name    : PositivityTheory.ThKF0.Grow.sobAbs
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:03:58.722806+00:00
-- url     : https://prove2.me/theorems/3c55d602-9c3e-4e8c-9dc1-084f80b90fae
-- title:
--   Grow: sob Abs
-- statement:
--   The Grow construction uses the sob Abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobA.lean#L66-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/GrowSobA.lean#L66-L108

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

theorem PositivityTheory.ThKF0.Grow.sobAbs {S : Set (X → ℂ)} (hS : ∀ Θ ∈ S, Continuous Θ) {dd : W → (X → ℂ) → X → ℂ}
    (hd : ∀ w, ∀ Θ ∈ S, dd w Θ ∈ S) (D : ℕ) : ∀ (ws : Fin D → W) (e : Fin D → ℝ →+ X), (∀ i, Continuous (e i)) →
      (∀ i, ∀ Θ ∈ S, ∀ x, HasDerivAt (fun t => Θ (x + e i t)) (dd (ws i) Θ x) 0) →
      ∃ L : List (List W), ∀ Θ ∈ S, ∀ x, ‖Θ x‖ₑ ^ 2 ≤ 2 ^ D * ∫⁻ t : Fin D → ℝ, sumSq dd L Θ (x + ∑ i, e i (t i)) := by sorry
