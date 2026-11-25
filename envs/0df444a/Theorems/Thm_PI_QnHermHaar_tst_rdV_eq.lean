-- Prove2me | Theorems.Thm_PI_QnHermHaar_tst_rdV_eq
-- name    : PI.QnHermHaar.tst_rdV_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:18:35.68261+00:00
-- url     : https://prove2.me/theorems/e74ce3a7-9ddd-42c4-9cb3-415403971a02
-- title:
--   Qn Herm Haar: tst rd V eq
-- statement:
--   The Qn Herm Haar construction uses the tst rd V eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorPreservesTest.lean#L212-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorPreservesTest.lean#L212-L232

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

theorem PI.QnHermHaar.tst_rdV_eq {k r : ℕ} {i : Fin (r + 1)} (f F : Mx k r → ℂ) (U : Set (Mx k r)) (g X : Mx k r)
    (hU : IsOpen U) (hg : g ∈ U) (hgG : g ∈ Glev k r i) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ h ∈ U, h ∈ Glev k r i → f h = F h) (hX : inLieLev k r i X) :
    RdV X f g = fderiv ℝ F g (g * X) := by sorry
