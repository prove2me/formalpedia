-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_det_sum__d17b9508e216
-- name    : P2M_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_det_sum__d17b9508e216
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:14:30.778069+00:00
-- url     : https://prove2.me/theorems/7d1b80de-7ae4-5489-beae-0ce730c095ca
-- title:
--   P2 M Formalism Fourier Decay Alt P Finite Sum Local Expansion det sum  d17b9508e216: P2 M Formalism Fourier Decay Alt P Finite Sum Local Expansion det sum  d17b9508e216
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Finite Sum Local Expansion det sum  d17b9508e216 construction uses the P2 M Formalism Fourier Decay Alt P Finite Sum Local Expansion det sum  d17b9508e216 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L319-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FiniteSumLocalExpansion.lean#L319-L322

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_det_sum__d17b9508e216 {t n : ℕ} (e : Fin t ≃ Fin n) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∑ τ : Equiv.Perm (Fin t), ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ j, A (e j) (e (τ j)) = A.det := by sorry

alias «Formalism».«FourierDecayAlt».«P».«FiniteSumLocalExpansion».«det_sum'» := P2M_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_det_sum__d17b9508e216
