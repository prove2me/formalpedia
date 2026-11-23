-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_isSS_of_decomp
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.isSS_of_decomp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:15.677314+00:00
-- url     : https://prove2.me/theorems/d1d7f807-4258-46e9-a404-0cd8bc95abfa
-- title:
--   Sep Fac: is SS of decomp
-- statement:
--   The Sep Fac construction uses the is SS of decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFac.lean#L34-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFac.lean#L34-L45

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

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.isSS_of_decomp {κ : Type} {x : A} (ι : Finset κ) (e : κ → A) (c : κ → ℂ) (hsum : ∑ i ∈ ι, e i = 1)
    (hx : ∀ i ∈ ι, x * e i = c i • e i) : IsSS x := by sorry
