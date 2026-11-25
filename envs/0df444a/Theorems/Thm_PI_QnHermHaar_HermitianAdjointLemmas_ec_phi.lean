-- Prove2me | Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_ec_phi
-- name    : PI.QnHermHaar.HermitianAdjointLemmas.ec_phi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:38:01.851002+00:00
-- url     : https://prove2.me/theorems/92f06db8-605a-593c-8361-085ba66d8f06
-- title:
--   Hermitian Adjoint Lemmas: ec phi
-- statement:
--   The Hermitian Adjoint Lemmas construction uses the ec phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorAdjoint.lean#L374-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorAdjoint.lean#L374-L379

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

theorem PI.QnHermHaar.HermitianAdjointLemmas.ec_phi {i : Fin (r + 1)} {L : Mx k r →L[ℝ] ℂ} {f : Mx k r → ℂ} {g : Mx k r}
    (hL : ∀ X, inLieLev k r i X → RdV X f g = L (g * X)) {W : Mx k r} (hW : SuppV i W) :
    RdV (hpart1 (Hpk k r) W) f g + Complex.I • RdV (hpart2 (Hpk k r) W) f g = phiL L g W := by sorry
