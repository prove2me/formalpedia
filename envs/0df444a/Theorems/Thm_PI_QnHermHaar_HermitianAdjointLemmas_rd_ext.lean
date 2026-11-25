-- Prove2me | Theorems.Thm_PI_QnHermHaar_HermitianAdjointLemmas_rd_ext
-- name    : PI.QnHermHaar.HermitianAdjointLemmas.rd_ext
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:36:28.056537+00:00
-- url     : https://prove2.me/theorems/873f3933-cd01-59a1-97a1-ccdeb7aa4a01
-- title:
--   Hermitian Adjoint Lemmas: rd ext
-- statement:
--   The Hermitian Adjoint Lemmas construction uses the rd ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorAdjoint.lean#L92-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/ElementaryGeneratorAdjoint.lean#L92-L112

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

theorem PI.QnHermHaar.HermitianAdjointLemmas.rd_ext {i : Fin (r + 1)} {f : Mx k r → ℂ} (hf : SmoothLev k r i Set.univ f) {g : Mx k r}
    (hg : g ∈ Glev k r i) : ∃ L : Mx k r →L[ℝ] ℂ, ∀ X, inLieLev k r i X → RdV X f g = L (g * X) := by sorry
