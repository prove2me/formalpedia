-- Prove2me | Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_glev_mul_exp
-- name    : PI.QnHermHaar.HermitianAdjointLemmas.glev_mul_exp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:16.442914+00:00
-- url     : https://prove2.me/theorems/25d7db4d-851a-4e30-bf77-bdf4ce464ddb
-- title:
--   Hermitian Adjoint Lemmas: glev mul exp
-- statement:
--   The Hermitian Adjoint Lemmas construction uses the glev mul exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorAdjoint.lean#L79-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorAdjoint.lean#L79-L90

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_ElementaryGeneratorAdjoint
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
open PI.QnHermHaar.HermitianAdjointLemmas
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem PI.QnHermHaar.HermitianAdjointLemmas.glev_mul_exp {i : Fin (r + 1)} {g X : Mx k r} (hg : g ∈ Glev k r i) (hX : inLieLev k r i X)
    (t : ℝ) : g * NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i := by sorry
