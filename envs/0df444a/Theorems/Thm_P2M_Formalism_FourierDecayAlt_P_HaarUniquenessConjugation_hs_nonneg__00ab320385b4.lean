-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_hs_nonneg__00ab320385b4
-- name    : P2M_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_hs_nonneg__00ab320385b4
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:56:11.841559+00:00
-- url     : https://prove2.me/theorems/9877075b-b982-4cbf-b74e-a6f231da7bb4
-- title:
--   P2 M Formalism Fourier Decay Alt P Haar Uniqueness Conjugation hs nonneg  00ab320385b4: P2 M Formalism Fourier Decay Alt P Haar Uniqueness Conjugation hs nonneg  00ab320385b4
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Haar Uniqueness Conjugation hs nonneg  00ab320385b4 construction uses the P2 M Formalism Fourier Decay Alt P Haar Uniqueness Conjugation hs nonneg  00ab320385b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarUniquenessConjugation.lean#L172-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarUniquenessConjugation.lean#L172-L172

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

theorem P2M_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_hs_nonneg__00ab320385b4 (g : Mat k r) : 0 ≤ hs g := by sorry

alias «Formalism».«FourierDecayAlt».«P».«HaarUniquenessConjugation».«hs_nonneg'» := P2M_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_hs_nonneg__00ab320385b4
