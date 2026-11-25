-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_IsSS_adjoin
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.IsSS.adjoin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:44.131178+00:00
-- url     : https://prove2.me/theorems/0246466b-6ae4-47fe-ae28-7b1b7926895f
-- title:
--   Is SS: adjoin
-- statement:
--   The Is SS construction uses the adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFacB.lean#L184-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFacB.lean#L184-L195

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFacB
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.IsSS.adjoin {s : Set A} (hs : ∀ x ∈ s, IsSS x) (hc : ∀ x ∈ s, ∀ y ∈ s, Commute x y) :
    ∀ y ∈ Algebra.adjoin ℂ s, IsSS y := by sorry
