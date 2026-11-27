-- Prove2me | Theorems.Thm_PositivityTheory_ThKCT_Arch_decay
-- name    : PositivityTheory.ThKCT.Arch.decay
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:59:06.324106+00:00
-- url     : https://prove2.me/theorems/49568ce8-5857-4554-bb2e-a1016529acaf
-- title:
--   Arch: decay
-- statement:
--   The Arch construction uses the decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L273-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SmallCones/SliceArch.lean#L273-L310

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem PositivityTheory.ThKCT.Arch.decay {Y Z : Type} [AddCommGroup Z] [Module ℂ Z] (A : Y → SchwartzMap V ℂ →ₗ[ℂ] Z) (s : Y → ℝ) (hs : ∀ y, 0 ≤ s y)
    (K : ℝ) (hK : ∀ y, 0 < s y → ∃ w, ‖w‖ * s y ≤ K ∧ ∀ f, A y (S w f) = -A y f) (q : Seminorm ℂ Z)
    (p : Seminorm ℂ (SchwartzMap V ℂ)) (hp : Continuous p) (M : ℕ) (hq : ∀ y f, q (A y f) ≤ (1 + s y) ^ M * p f) (N : ℕ) :
    ∃ p' : Seminorm ℂ (SchwartzMap V ℂ), Continuous p' ∧ ∀ y f, q (A y f) * (1 + s y) ^ N ≤ p' f := by sorry
