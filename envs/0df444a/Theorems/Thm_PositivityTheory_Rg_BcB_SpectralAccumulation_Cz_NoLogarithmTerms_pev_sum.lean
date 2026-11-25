-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_NoLogarithmTerms_pev_sum
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms.pev_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:53:02.866747+00:00
-- url     : https://prove2.me/theorems/a2760456-2d3a-4ed8-b90a-02265d2795aa
-- title:
--   No Logarithm Terms: pev sum
-- statement:
--   The No Logarithm Terms construction uses the pev sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PNoLogOde.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PNoLogOde.lean#L23-L25

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

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms.pev_sum {ι : Type} (s : Finset ι) (p : ι → ℂ[X]) (f : ℕ → ℝ → ℂ) (t : ℝ) :
    pev (∑ i ∈ s, p i) f t = ∑ i ∈ s, pev (p i) f t := by sorry
