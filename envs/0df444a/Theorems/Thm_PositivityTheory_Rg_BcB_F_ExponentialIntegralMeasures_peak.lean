-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_F_ExponentialIntegralMeasures_peak
-- name    : PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.peak
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:52:35.276214+00:00
-- url     : https://prove2.me/theorems/2f2cfd82-2831-5af4-953d-94ca77ac59ef
-- title:
--   Exponential Integral Measures: peak
-- statement:
--   The Exponential Integral Measures construction uses the peak property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/PeakTraceBoundHolds.lean#L217-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/PeakTraceBoundHolds.lean#L217-L363

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSumStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures

theorem PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.peak {A : Type} [CommRing A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)]
    [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)]
    (R : ∀ s, A →⋆ₐ[ℂ] (H s →L[ℂ] H s)) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (p : A →⋆ₐ[ℂ] ℂ)
    (hβ : ∀ s g, Commute (β s) (R s g))
    (hne : ∀ s (χ : StarAlgebra.adjoin ℂ (Set.range (R s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
      (∀ x, ‖χ x‖ ≤ ‖(x : H s →L[ℂ] H s)‖) →
      (∀ g, χ ⟨R s g, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)⟩ = p g) →
      χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ = 0)
    (ε : ℝ) (hε : 0 < ε) : ∃ g : A, p g = 1 ∧ ∀ s, ‖β s ^ m * R s g‖ ≤ ε := by sorry
