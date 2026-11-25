-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux4_w_w_mul__3756fc73a85d
-- name    : P2M_Formalism_FourierDecayAlt_P_Ux4_w_w_mul__3756fc73a85d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:05.210843+00:00
-- url     : https://prove2.me/theorems/1823198a-0567-44c9-acea-03d86415dbc7
-- title:
--   P2 M Formalism Fourier Decay Alt P Ux4 w w mul  3756fc73a85d: P2 M Formalism Fourier Decay Alt P Ux4 w w mul  3756fc73a85d
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Ux4 w w mul  3756fc73a85d construction uses the P2 M Formalism Fourier Decay Alt P Ux4 w w mul  3756fc73a85d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L169-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L169-L170

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}

theorem P2M_Formalism_FourierDecayAlt_P_Ux4_w_w_mul__3756fc73a85d {n : ℕ} (M : Matrix (Fin j) (Fin n) ℂ) : G.wMat j * (G.wMat j * M) = M := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Ux4».«w_w_mul'» := P2M_Formalism_FourierDecayAlt_P_Ux4_w_w_mul__3756fc73a85d
