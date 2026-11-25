-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_SpectralAccumulation_Cz_SepFac_IsSS_exists_decomp
-- name    : PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.IsSS.exists_decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:09.615802+00:00
-- url     : https://prove2.me/theorems/96b01d3d-4afc-4a2d-98a9-1f1fcd3a2ae1
-- title:
--   Is SS: exists decomp
-- statement:
--   The Is SS construction uses the exists decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFac.lean#L47-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PSepFac.lean#L47-L64

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

theorem PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.IsSS.exists_decomp {x : A} (hx : IsSS x) : ∃ (s : Finset ℂ) (e : ℂ → A), ∑ v ∈ s, e v = 1 ∧
    (∀ v ∈ s, x * e v = v • e v) ∧ ∀ v, ∀ y : A, Commute x y → Commute (e v) y := by sorry
