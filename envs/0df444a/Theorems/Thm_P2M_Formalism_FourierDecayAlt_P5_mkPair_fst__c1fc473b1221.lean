-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P5_mkPair_fst__c1fc473b1221
-- name    : P2M_Formalism_FourierDecayAlt_P5_mkPair_fst__c1fc473b1221
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:44.369484+00:00
-- url     : https://prove2.me/theorems/8dd6e19a-56df-40d5-bd90-bddd415f9cbe
-- title:
--   P2 M Formalism Fourier Decay Alt P5 mk Pair fst  c1fc473b1221: P2 M Formalism Fourier Decay Alt P5 mk Pair fst  c1fc473b1221
-- statement:
--   The P2 M Formalism Fourier Decay Alt P5 mk Pair fst  c1fc473b1221 construction uses the P2 M Formalism Fourier Decay Alt P5 mk Pair fst  c1fc473b1221 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L136-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L136-L136

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem P2M_Formalism_FourierDecayAlt_P5_mkPair_fst__c1fc473b1221 (X Xs : Module.End ℂ V) : (mkP X Xs : Pr V).1 = X := by sorry

alias «Formalism».«FourierDecayAlt».«P5».«mkPair_fst'» := P2M_Formalism_FourierDecayAlt_P5_mkPair_fst__c1fc473b1221

attribute [defeq] P2M_Formalism_FourierDecayAlt_P5_mkPair_fst__c1fc473b1221
