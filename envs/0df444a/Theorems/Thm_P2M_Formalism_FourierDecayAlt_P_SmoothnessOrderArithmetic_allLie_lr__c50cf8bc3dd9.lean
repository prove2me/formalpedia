-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_allLie_lr__c50cf8bc3dd9
-- name    : P2M_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_allLie_lr__c50cf8bc3dd9
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:30:44.746691+00:00
-- url     : https://prove2.me/theorems/11e3dd64-d496-406f-9600-d7b0e0039df6
-- title:
--   P2 M Formalism Fourier Decay Alt P Smoothness Order Arithmetic all Lie lr  c50cf8bc3dd9: P2 M Formalism Fourier Decay Alt P Smoothness Order Arithmetic all Lie lr  c50cf8bc3dd9
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Smoothness Order Arithmetic all Lie lr  c50cf8bc3dd9 construction uses the P2 M Formalism Fourier Decay Alt P Smoothness Order Arithmetic all Lie lr  c50cf8bc3dd9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DerivativeRulesA1.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DerivativeRulesA1.lean#L68-L74

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivativeRulesA1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_allLie_lr__c50cf8bc3dd9 {u v : List (Mat k r)} (hu : ∀ X ∈ u, inLie k r X) (hv : ∀ X ∈ v, inLie k r X) :
    AllLie (lr u v) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«SmoothnessOrderArithmetic».«allLie_lr'» := P2M_Formalism_FourierDecayAlt_P_SmoothnessOrderArithmetic_allLie_lr__c50cf8bc3dd9
