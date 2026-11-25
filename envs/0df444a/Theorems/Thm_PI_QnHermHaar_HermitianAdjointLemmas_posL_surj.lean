-- Prove2me | Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_posL_surj
-- name    : PI.QnHermHaar.HermitianAdjointLemmas.posL_surj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:36:55.61245+00:00
-- url     : https://prove2.me/theorems/856d1733-1219-43d5-b40f-15276e7a5f66
-- title:
--   Hermitian Adjoint Lemmas: pos L surj
-- statement:
--   The Hermitian Adjoint Lemmas construction uses the pos L surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorAdjoint.lean#L332-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorAdjoint.lean#L332-L338

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

theorem PI.QnHermHaar.HermitianAdjointLemmas.posL_surj {i : Fin (r + 1)} {p : Fin (2 * r + k + 1)} (hp : ¬ Out i p) :
    ∃ c : Fin (mdim k r i), posL k r i c = p := by sorry
