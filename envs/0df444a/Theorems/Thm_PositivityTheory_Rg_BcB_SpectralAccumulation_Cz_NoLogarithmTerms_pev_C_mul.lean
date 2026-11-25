-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_NoLogarithmTerms_pev_C_mul
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms.pev_C_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:42.146007+00:00
-- url     : https://prove2.me/theorems/a6ff8c64-c5f8-5e02-8bfb-db9b1d7aec38
-- title:
--   No Logarithm Terms: pev C mul
-- statement:
--   The No Logarithm Terms construction uses the pev C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PNoLogOde.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PNoLogOde.lean#L20-L21

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

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms.pev_C_mul (c : ℂ) (p : ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) : pev (C c * p) f t = c * pev p f t := by sorry
