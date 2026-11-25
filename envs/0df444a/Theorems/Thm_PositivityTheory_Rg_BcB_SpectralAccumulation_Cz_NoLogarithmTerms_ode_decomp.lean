-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_NoLogarithmTerms_ode_decomp
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms.ode_decomp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:32.213615+00:00
-- url     : https://prove2.me/theorems/03d22a43-f151-4973-8266-9deef0a61c0c
-- title:
--   No Logarithm Terms: ode decomp
-- statement:
--   The No Logarithm Terms construction uses the ode decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PNoLogOde.lean#L65-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PNoLogOde.lean#L65-L89

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PNoLogOde
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms.ode_decomp (S : Finset ℂ) : ∃ L : ℂ → ℂ[X], ∀ f : ℕ → ℝ → ℂ, (∀ k t, HasDerivAt (f k) (f (k + 1) t) t) →
    (∀ t, pev (∏ v ∈ S, (X - C v)) f t = 0) →
    (∀ t, f 0 t = ∑ v ∈ S, pev (L v) f t) ∧ ∀ v ∈ S, ∀ t, pev (L v) f t = Complex.exp (v * t) * pev (L v) f 0 := by sorry
