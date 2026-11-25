-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx5_single_mulVec__ad7365b648dd
-- name    : P2M_Formalism_FourierDecayAlt_P_Qx5_single_mulVec__ad7365b648dd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:45:33.489947+00:00
-- url     : https://prove2.me/theorems/1fd777a4-a98f-4298-b3a5-f429904fcbdf
-- title:
--   P2 M Formalism Fourier Decay Alt P Qx5 single mul Vec  ad7365b648dd: P2 M Formalism Fourier Decay Alt P Qx5 single mul Vec  ad7365b648dd
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Qx5 single mul Vec  ad7365b648dd construction uses the P2 M Formalism Fourier Decay Alt P Qx5 single mul Vec  ad7365b648dd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1645-L1652
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ActualAdjointnessFromHermitian.lean#L1645-L1652

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
open Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem P2M_Formalism_FourierDecayAlt_P_Qx5_single_mulVec__ad7365b648dd (p q : Fin (2 * r + k + 1)) (u : Fin (2 * r + k + 1) → ℂ) :
    (Matrix.single p q (1 : ℂ) : Mx k r) *ᵥ u = u q • bvec p := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Qx5».«single_mulVec'» := P2M_Formalism_FourierDecayAlt_P_Qx5_single_mulVec__ad7365b648dd
