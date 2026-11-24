-- Prove2me | Theorems.Thm_P2M_RH_Formalism_FourierDecayAlt_P5_contDiff_fsv_96a9e73be49d280f
-- name    : P2M_RH_Formalism_FourierDecayAlt_P5_contDiff_fsv_96a9e73be49d280f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:09.347134+00:00
-- url     : https://prove2.me/theorems/8894d395-2007-444e-bac1-860fe9037435
-- title:
--   P2 M RH Formalism Fourier Decay Alt P5 cont Diff fsv 96a9e73be49d280f: P2 M RH Formalism Fourier Decay Alt P5 cont Diff fsv 96a9e73be49d280f
-- statement:
--   The P2 M RH Formalism Fourier Decay Alt P5 cont Diff fsv 96a9e73be49d280f construction uses the P2 M RH Formalism Fourier Decay Alt P5 cont Diff fsv 96a9e73be49d280f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermMulVecMulVec.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermMulVecMulVec.lean#L56-L59

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermMulVecMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ComplexOrder ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem P2M_RH_Formalism_FourierDecayAlt_P5_contDiff_fsv_96a9e73be49d280f (s : ℂ) : ContDiff ℝ ∞ (fsv s) := by sorry

alias «Formalism».«FourierDecayAlt».«P5».«contDiff_fsv» := P2M_RH_Formalism_FourierDecayAlt_P5_contDiff_fsv_96a9e73be49d280f
