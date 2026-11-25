-- Prove2me | Theorems.Thm_PositivityTheory_RgFd_mom_step
-- name    : PositivityTheory.RgFd.mom_step
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:03:03.611811+00:00
-- url     : https://prove2.me/theorems/ffc6b64d-40a8-46b4-91e7-abcd56d6aaed
-- title:
--   Rg Fd: mom step
-- statement:
--   The Rg Fd construction uses the mom step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/FormalDegree/FormalDegreeHilbert/MomentRecursion/MomStep.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/FormalDegree/FormalDegreeHilbert/MomentRecursion/MomStep.lean#L7-L32

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_FormalDegree_FormalDegreeHilbert_MomB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_FormalDegree_FormalDegreeHilbert_MomentRecursion_MomStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open PositivityTheory PositivityTheory.RgFd

theorem PositivityTheory.RgFd.mom_step {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {ν : Measure Ω} {ν' : Measure Ω'} {V : Ω → ℝ}
    {V' : Ω' → ℝ} (hV : Measurable V) (hV' : Measurable V') (h0 : ∀ x, 0 ≤ V x ∧ V x ≤ 1) (h0' : ∀ y, 0 ≤ V' y ∧ V' y ≤ 1)
    (he : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (V x ^ j) ∂ν = ∫⁻ y, ENNReal.ofReal (V' y ^ j) ∂ν')
    (hf : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (V x ^ j) ∂ν ≠ ⊤) (M : ℕ) : ∀ j : ℕ, 1 ≤ j →
    ∫⁻ x, ENNReal.ofReal (V x ^ j * (1 - V x) ^ M) ∂ν = ∫⁻ y, ENNReal.ofReal (V' y ^ j * (1 - V' y) ^ M) ∂ν' := by sorry
