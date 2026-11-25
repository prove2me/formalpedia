-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_Glob_DerOneAbsH_integral_deriv_zero
-- name    : PositivityTheory.Rg.Sw.Glob.DerOneAbsH.integral_deriv_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:52:54.034625+00:00
-- url     : https://prove2.me/theorems/f117a6a2-ea03-489e-9c3b-25fa75ae9404
-- title:
--   Der One Abs H: integral deriv zero
-- statement:
--   The Der One Abs H construction uses the integral deriv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/DerOneAbs.lean#L9-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GlobalGaussLaws/DerOneAbs.lean#L9-L89

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_DerOneAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory intervalIntegral
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.DerOneAbsH

theorem PositivityTheory.Rg.Sw.Glob.DerOneAbsH.integral_deriv_zero {X Ξ : Type*} [MeasurableSpace X] [Countable Ξ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (m : Measure X) [SFinite m] (F F' : X → ℝ → Ξ → ℂ)
    (hd : ∀ x ξ, ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s => F x s ξ) (F' x t ξ) t)
    (hcont : ∀ x ξ, Continuous fun t => F' x t ξ)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun p : X × ℝ => F' p.1 p.2 ξ) (m.prod (volume.restrict (Set.Ioc 0 1))))
    (hfin : ∫⁻ p : X × ℝ, ∑' ξ, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod (volume.restrict (Set.Ioc 0 1))) ≠ ⊤)
    (hsum0 : ∀ᵐ x ∂m, Summable fun ξ => ‖F x 0 ξ‖) (hsum1 : ∀ᵐ x ∂m, Summable fun ξ => ‖F x 1 ξ‖)
    (hint0 : Integrable (fun x => ∑' ξ, F x 0 ξ) m) (hint1 : Integrable (fun x => ∑' ξ, F x 1 ξ) m)
    (hends : ∫ x, ∑' ξ, F x 1 ξ ∂m = ∫ x, ∑' ξ, F x 0 ξ ∂m)
    (hconst : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∫ x, ∑' ξ, F' x t ξ ∂m = ∫ x, ∑' ξ, F' x 0 ξ ∂m) :
    ∫ x, ∑' ξ, F' x 0 ξ ∂m = 0 := by sorry
