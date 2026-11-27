-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Rs_StrStepA_step_down
-- name    : PositivityTheory.Rg.Rs.StrStepA.step_down
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:52:03.645222+00:00
-- url     : https://prove2.me/theorems/dfc7a053-03b1-5354-ae65-c2c533e0b97d
-- title:
--   Str Step A: step down
-- statement:
--   The Str Step A construction uses the step down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/SdNormCpow.lean#L9-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ResidualSpectrum/SliceTensors/SdNormCpow.lean#L9-L77

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_SdNormCpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.StrStepA

theorem PositivityTheory.Rg.Rs.StrStepA.step_down (q : ℕ) (hq : 1 < q) (B₀ : Multiset ℂ)
    (hB : ∀ β ∈ B₀, (q : ℝ) ^ (-(1 / 2) : ℝ) < ‖β‖ ∧ ‖β‖ < (q : ℝ) ^ (1 / 2 : ℝ)) {α : ℂ} (hα : α ∈ B₀)
    (S : Set ℝ) (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, x - y = n) (M : Multiset ℂ)
    (hM : ∀ z, z ∈ M ↔ ∃ x ∈ S, ∃ β ∈ B₀, z = β * (q : ℂ) ^ (-(x : ℂ)))
    (hgap : ∀ z : ℂ, ‖z‖ < (q : ℝ) ^ (-(1 / 2) : ℝ) → M.count z ≤ M.count ((q : ℂ) * z))
    {u : ℝ} (hu : u ∈ S) (hu1 : 1 ≤ u) : u - 1 ∈ S := by sorry
