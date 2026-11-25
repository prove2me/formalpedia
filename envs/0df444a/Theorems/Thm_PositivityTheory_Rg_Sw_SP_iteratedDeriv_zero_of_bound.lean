-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_iteratedDeriv_zero_of_bound
-- name    : PositivityTheory.Rg.Sw.SP.iteratedDeriv_zero_of_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:18.109057+00:00
-- url     : https://prove2.me/theorems/2a1f49f3-27fe-43f9-94c5-30f4ab2026b0
-- title:
--   SP: iterated Deriv zero of bound
-- statement:
--   The SP construction uses the iterated Deriv zero of bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/IteratedDerivZeroOfBound.lean#L9-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/IteratedDerivZeroOfBound.lean#L9-L37

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_IteratedDerivZeroOfBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP

theorem PositivityTheory.Rg.Sw.SP.iteratedDeriv_zero_of_bound {f : ℂ → ℂ} {ε C : ℝ} {r : ℕ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (ball 0 ε)) (hb : ∀ z ∈ ball (0 : ℂ) ε, ‖f z‖ ≤ C * ‖z‖ ^ r) {j : ℕ} (hj : j < r) :
    iteratedDeriv j f 0 = 0 := by sorry
