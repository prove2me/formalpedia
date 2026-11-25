-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_F_ExponentialIntegralMeasures_restr
-- name    : PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.restr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:12.297132+00:00
-- url     : https://prove2.me/theorems/91a2daef-a6d2-431e-a9a1-ad256a901dda
-- title:
--   Exponential Integral Measures: restr
-- statement:
--   The Exponential Integral Measures construction uses the restr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/PeakTraceBoundHolds.lean#L18-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/SatakeExponents/UniformizerValuations/PeakTraceBoundHolds.lean#L18-L33

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

theorem PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.restr (S : StarSubalgebra ℂ E) (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (ψ : S.topologicalClosure →ₐ[ℂ] ℂ) :
    ∃ χ : S →⋆ₐ[ℂ] ℂ, (∀ y, ‖χ y‖ ≤ ‖(y : E)‖) ∧
      ∀ y, χ y = ψ (StarSubalgebra.inclusion S.le_topologicalClosure y) := by sorry
