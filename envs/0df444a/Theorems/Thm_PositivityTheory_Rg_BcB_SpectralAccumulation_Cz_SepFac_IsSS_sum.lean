-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_IsSS_sum
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.IsSS.sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:47:58.93309+00:00
-- url     : https://prove2.me/theorems/fde2d2c6-197a-4126-859e-99811f83dd60
-- title:
--   Is SS: sum
-- statement:
--   The Is SS construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFac.lean#L109-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFac.lean#L109-L120

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
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

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.IsSS.sum {κ : Type} (ι : Finset κ) (x : κ → A) (hx : ∀ i ∈ ι, IsSS (x i))
    (hc : ∀ i ∈ ι, ∀ j ∈ ι, Commute (x i) (x j)) : IsSS (∑ i ∈ ι, x i) := by sorry
