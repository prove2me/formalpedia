-- Prove2me | Theorems.Thm_PI_QnHermHaar_tst_mul_test
-- name    : PI.QnHermHaar.tst_mul_test
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:19:04.834304+00:00
-- url     : https://prove2.me/theorems/7f67ccb1-279b-435f-bd8d-838d9603b44d
-- title:
--   Qn Herm Haar: tst mul test
-- statement:
--   The Qn Herm Haar construction uses the tst mul test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorPreservesTest.lean#L276-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorPreservesTest.lean#L276-L287

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorPreservesTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem PI.QnHermHaar.tst_mul_test {k r : ℕ} {i : Fin (r + 1)} (φ ψ : Mx k r → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (hψ : ∀ g ∈ Glev k r i, ψ g = φ g) (f : Mx k r → ℂ) (hf : TestF k r i f) :
    TestF k r i (fun g => ψ g * f g) := by sorry
