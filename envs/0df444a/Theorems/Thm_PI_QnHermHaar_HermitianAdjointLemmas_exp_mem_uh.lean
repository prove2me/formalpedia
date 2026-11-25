-- Prove2me | Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_exp_mem_uh
-- name    : PI.QnHermHaar.HermitianAdjointLemmas.exp_mem_uh
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:59:58.789213+00:00
-- url     : https://prove2.me/theorems/cb55d2d2-1077-42ca-8644-c40da7cc9b19
-- title:
--   Hermitian Adjoint Lemmas: exp mem uh
-- statement:
--   The Hermitian Adjoint Lemmas construction uses the exp mem uh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorAdjoint.lean#L65-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorAdjoint.lean#L65-L77

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

theorem PI.QnHermHaar.HermitianAdjointLemmas.exp_mem_uh {Y : Mx k r} (hY : Yᴴ * Hpk k r + Hpk k r * Y = 0) :
    NormedSpace.exp Y ∈ UH (Hpk k r) := by sorry
