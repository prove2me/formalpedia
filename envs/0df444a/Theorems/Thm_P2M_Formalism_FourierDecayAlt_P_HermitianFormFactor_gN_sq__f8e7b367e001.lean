-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HermitianFormFactor_gN_sq__f8e7b367e001
-- name    : P2M_Formalism_FourierDecayAlt_P_HermitianFormFactor_gN_sq__f8e7b367e001
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:55:58.899657+00:00
-- url     : https://prove2.me/theorems/1503c9ac-88c9-4ee7-8a32-5aabb557d1f6
-- title:
--   P2 M Formalism Fourier Decay Alt P Hermitian Form Factor g N sq  f8e7b367e001: P2 M Formalism Fourier Decay Alt P Hermitian Form Factor g N sq  f8e7b367e001
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Hermitian Form Factor g N sq  f8e7b367e001 construction uses the P2 M Formalism Fourier Decay Alt P Hermitian Form Factor g N sq  f8e7b367e001 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1639-L1640
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L1639-L1640

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise

theorem P2M_Formalism_FourierDecayAlt_P_HermitianFormFactor_gN_sq__f8e7b367e001 {k r : ℕ} (A : Mat k r) : gN A ^ 2 = ∑ i, ∑ j, Complex.normSq (A i j) := by sorry

alias «Formalism».«FourierDecayAlt».«P».«HermitianFormFactor».«gN_sq'» := P2M_Formalism_FourierDecayAlt_P_HermitianFormFactor_gN_sq__f8e7b367e001
