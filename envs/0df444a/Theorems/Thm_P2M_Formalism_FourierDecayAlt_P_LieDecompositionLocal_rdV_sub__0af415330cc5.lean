-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_sub__0af415330cc5
-- name    : P2M_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_sub__0af415330cc5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:56:00.971688+00:00
-- url     : https://prove2.me/theorems/c2e63922-0e0d-45bf-8397-d92093a6fc0c
-- title:
--   P2 M Formalism Fourier Decay Alt P Lie Decomposition Local rd V sub  0af415330cc5: P2 M Formalism Fourier Decay Alt P Lie Decomposition Local rd V sub  0af415330cc5
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Lie Decomposition Local rd V sub  0af415330cc5 construction uses the P2 M Formalism Fourier Decay Alt P Lie Decomposition Local rd V sub  0af415330cc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L131-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LieDecompositionLocal.lean#L131-L136

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LieDecompositionLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_sub__0af415330cc5 {Φ : Mat k r → E} {g X Y : Mat k r} (hloc : Loc 1 Φ g) (hgG : g ∈ GV k r)
    (hX : inLie k r X) (hY : inLie k r Y) : RdV (X - Y) Φ g = RdV X Φ g - RdV Y Φ g := by sorry

alias «Formalism».«FourierDecayAlt».«P».«LieDecompositionLocal».«rdV_sub'» := P2M_Formalism_FourierDecayAlt_P_LieDecompositionLocal_rdV_sub__0af415330cc5
