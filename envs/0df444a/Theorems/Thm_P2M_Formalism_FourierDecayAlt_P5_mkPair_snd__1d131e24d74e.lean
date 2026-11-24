-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P5_mkPair_snd__1d131e24d74e
-- name    : P2M_Formalism_FourierDecayAlt_P5_mkPair_snd__1d131e24d74e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:27:44.92629+00:00
-- url     : https://prove2.me/theorems/bd298ae8-883c-48ce-a643-1aa6089e0faa
-- title:
--   P2 M Formalism Fourier Decay Alt P5 mk Pair snd  1d131e24d74e: P2 M Formalism Fourier Decay Alt P5 mk Pair snd  1d131e24d74e
-- statement:
--   The P2 M Formalism Fourier Decay Alt P5 mk Pair snd  1d131e24d74e construction uses the P2 M Formalism Fourier Decay Alt P5 mk Pair snd  1d131e24d74e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L137-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FsvMulFsvNeg.lean#L137-L137

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

theorem P2M_Formalism_FourierDecayAlt_P5_mkPair_snd__1d131e24d74e (X Xs : Module.End ℂ V) : (mkP X Xs : Pr V).2.unop = Xs := by sorry

alias «Formalism».«FourierDecayAlt».«P5».«mkPair_snd'» := P2M_Formalism_FourierDecayAlt_P5_mkPair_snd__1d131e24d74e

attribute [defeq] P2M_Formalism_FourierDecayAlt_P5_mkPair_snd__1d131e24d74e
