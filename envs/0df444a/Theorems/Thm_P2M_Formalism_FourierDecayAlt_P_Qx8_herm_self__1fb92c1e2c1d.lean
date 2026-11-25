-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx8_herm_self__1fb92c1e2c1d
-- name    : P2M_Formalism_FourierDecayAlt_P_Qx8_herm_self__1fb92c1e2c1d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:28:33.443806+00:00
-- url     : https://prove2.me/theorems/692935c1-abf1-424f-857c-1eaa0881cf3c
-- title:
--   P2 M Formalism Fourier Decay Alt P Qx8 herm self  1fb92c1e2c1d: P2 M Formalism Fourier Decay Alt P Qx8 herm self  1fb92c1e2c1d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Qx8 herm self  1fb92c1e2c1d construction uses the P2 M Formalism Fourier Decay Alt P Qx8 herm self  1fb92c1e2c1d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictionIrrelevantDoubleLevelOperator.lean#L2877-L2878
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictionIrrelevantDoubleLevelOperator.lean#L2877-L2878

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulIntegralStatement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_Qx8_herm_self__1fb92c1e2c1d (z : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Qx8».«herm_self'» := P2M_Formalism_FourierDecayAlt_P_Qx8_herm_self__1fb92c1e2c1d
