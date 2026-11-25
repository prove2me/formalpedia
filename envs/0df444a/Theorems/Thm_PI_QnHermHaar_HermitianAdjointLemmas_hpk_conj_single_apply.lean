-- Prove2me | Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_hpk_conj_single_apply
-- name    : PI.QnHermHaar.HermitianAdjointLemmas.hpk_conj_single_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:00:17.202569+00:00
-- url     : https://prove2.me/theorems/8e83ad34-8be6-4aeb-a5c1-431ad34e79bf
-- title:
--   Hermitian Adjoint Lemmas: hpk conj single apply
-- statement:
--   The Hermitian Adjoint Lemmas construction uses the hpk conj single apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorAdjoint.lean#L307-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorAdjoint.lean#L307-L310

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

theorem PI.QnHermHaar.HermitianAdjointLemmas.hpk_conj_single_apply (a' b' p q : Fin (2 * r + k + 1)) :
    (Hpk k r * (Matrix.single a' b' (1 : ℂ))ᴴ * Hpk k r) p q = Hpk k r p b' * Hpk k r a' q := by sorry
