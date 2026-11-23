-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_NoLogarithmTerms_pev_eq
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms.pev_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:22.523445+00:00
-- url     : https://prove2.me/theorems/994c9df9-34a1-4f04-ad72-f06cd862a124
-- title:
--   No Logarithm Terms: pev eq
-- statement:
--   The No Logarithm Terms construction uses the pev eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PNoLogOde.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PNoLogOde.lean#L13-L15

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

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms.pev_eq (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev p f t = pevL f t p := by sorry
