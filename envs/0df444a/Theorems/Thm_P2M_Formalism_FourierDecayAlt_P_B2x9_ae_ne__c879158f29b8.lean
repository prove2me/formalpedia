-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x9_ae_ne__c879158f29b8
-- name    : P2M_Formalism_FourierDecayAlt_P_B2x9_ae_ne__c879158f29b8
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:21.445803+00:00
-- url     : https://prove2.me/theorems/463a6491-83a6-4c2c-9f99-0e0ec5bbdcc4
-- title:
--   P2 M Formalism Fourier Decay Alt P B2x9 ae ne  c879158f29b8: P2 M Formalism Fourier Decay Alt P B2x9 ae ne  c879158f29b8
-- statement:
--   The P2 M Formalism Fourier Decay Alt P B2x9 ae ne  c879158f29b8 construction uses the P2 M Formalism Fourier Decay Alt P B2x9 ae ne  c879158f29b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianLeviVectorBaseOrthogonal.lean#L636-L652
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianLeviVectorBaseOrthogonal.lean#L636-L652

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_B2x9_ae_ne__c879158f29b8 (CI : ConeInv) (a : Mat k (1 + r')) (ha : a ∈ GV k (1 + r')) :
    ∀ᵐ p : ℂ × HPar k r' ∂(mCone k r'), (a *ᵥ xi k r' p) (iL k r') ≠ 0 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«B2x9».«ae_ne'» := P2M_Formalism_FourierDecayAlt_P_B2x9_ae_ne__c879158f29b8
