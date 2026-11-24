-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_gFromDiag__623203fd9e2d
-- name    : P2M_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_gFromDiag__623203fd9e2d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:37:21.79481+00:00
-- url     : https://prove2.me/theorems/8b81d0d9-55a0-4ed7-a742-b7f3e094b147
-- title:
--   P2 M Formalism Fourier Decay Alt P Haar Uniqueness Conjugation g From Diag  623203fd9e2d: P2 M Formalism Fourier Decay Alt P Haar Uniqueness Conjugation g From Diag  623203fd9e2d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Haar Uniqueness Conjugation g From Diag  623203fd9e2d construction uses the P2 M Formalism Fourier Decay Alt P Haar Uniqueness Conjugation g From Diag  623203fd9e2d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarUniquenessConjugation.lean#L239-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarUniquenessConjugation.lean#L239-L247

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}

theorem P2M_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_gFromDiag__623203fd9e2d (hE : UJEmb) (hU : Unimodular) (hV : VolGrowth) (hF : HpkFacts) (hC : UHConj) :
    HaarGExists ∧ VolCrude := by sorry

alias «Formalism».«FourierDecayAlt».«P».«HaarUniquenessConjugation».«gFromDiag'» := P2M_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_gFromDiag__623203fd9e2d
