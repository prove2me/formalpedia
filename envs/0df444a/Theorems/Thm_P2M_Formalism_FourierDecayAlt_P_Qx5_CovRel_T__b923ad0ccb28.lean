-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx5_CovRel_T__b923ad0ccb28
-- name    : P2M_Formalism_FourierDecayAlt_P_Qx5_CovRel_T__b923ad0ccb28
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:37:03.08671+00:00
-- url     : https://prove2.me/theorems/d54e9a49-faa8-40ab-81ab-18e725d8a433
-- title:
--   P2 M Formalism Fourier Decay Alt P Qx5 Cov Rel T  b923ad0ccb28: P2 M Formalism Fourier Decay Alt P Qx5 Cov Rel T  b923ad0ccb28
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Qx5 Cov Rel T  b923ad0ccb28 construction uses the P2 M Formalism Fourier Decay Alt P Qx5 Cov Rel T  b923ad0ccb28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L852-L862
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L852-L862

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
variable {E : Fin n → Fin n → A} {η : Fin n → A} {x : Fin n → ℂ} {ζ : A}

theorem P2M_Formalism_FourierDecayAlt_P_Qx5_CovRel_T__b923ad0ccb28 (h : CovRel E η x ζ) (w : ℂ) (a b c : Fin n) :
    Tm E w a b * η c = η c * Tm E (w - 1) a b + (if a = b then η c else 0) + (if b = c then η a else 0) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Qx5».«CovRel».«Tη» := P2M_Formalism_FourierDecayAlt_P_Qx5_CovRel_T__b923ad0ccb28
