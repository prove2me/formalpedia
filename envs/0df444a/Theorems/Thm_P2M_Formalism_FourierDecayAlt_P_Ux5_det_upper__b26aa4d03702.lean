-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux5_det_upper__b26aa4d03702
-- name    : P2M_Formalism_FourierDecayAlt_P_Ux5_det_upper__b26aa4d03702
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:22.486269+00:00
-- url     : https://prove2.me/theorems/61de9d3a-bb13-4690-b71e-dbbb299ed0d4
-- title:
--   P2 M Formalism Fourier Decay Alt P Ux5 det upper  b26aa4d03702: P2 M Formalism Fourier Decay Alt P Ux5 det upper  b26aa4d03702
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Ux5 det upper  b26aa4d03702 construction uses the P2 M Formalism Fourier Decay Alt P Ux5 det upper  b26aa4d03702 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L220-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L220-L226

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5

theorem P2M_Formalism_FourierDecayAlt_P_Ux5_det_upper__b26aa4d03702 {p : ℕ} (u : G.UT p → ℂ) : (G.upper u).det = 1 := by sorry

alias «Formalism».«FourierDecayAlt».«P».«Ux5».«det_upper'» := P2M_Formalism_FourierDecayAlt_P_Ux5_det_upper__b26aa4d03702
