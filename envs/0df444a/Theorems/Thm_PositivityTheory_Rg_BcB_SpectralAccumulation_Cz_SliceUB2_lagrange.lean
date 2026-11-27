-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SliceUB2_lagrange
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2.lagrange
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:52:43.044461+00:00
-- url     : https://prove2.me/theorems/f3e471f4-2964-4d2e-a021-ed4c09a212fa
-- title:
--   Slice UB2: lagrange
-- statement:
--   The Slice UB2 construction uses the lagrange property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/ExpChar.lean#L13-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/ExpChar.lean#L13-L60

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_ExpChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SliceUB2.lagrange (C : Finset ℂ) (c : ℂ) : ∃ (τs : Finset ℝ) (a : ℝ → ℂ), ∀ c' ∈ C,
    ∑ t ∈ τs, a t * Complex.exp (c' * t) = if c' = c then 1 else 0 := by sorry
