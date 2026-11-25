-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_F_ExponentialIntegralMeasures_norm_le_of_chars
-- name    : PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.norm_le_of_chars
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:52:14.572356+00:00
-- url     : https://prove2.me/theorems/74a29563-1105-568d-8b12-c0400c654fb6
-- title:
--   Exponential Integral Measures: norm le of chars
-- statement:
--   The Exponential Integral Measures construction uses the norm le of chars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/PeakTraceBoundHolds.lean#L35-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/PeakTraceBoundHolds.lean#L35-L50

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
variable {E : Type*} [CStarAlgebra E]

theorem PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.norm_le_of_chars (S : StarSubalgebra ℂ E) (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (x : E) (hx : x ∈ S) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ ψ : S.topologicalClosure →ₐ[ℂ] ℂ,
      ‖ψ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨x, hx⟩)‖ ≤ c) : ‖x‖ ≤ c := by sorry
