-- Prove2me | Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_SignAntidiagonal_sg_val__ef8cc9865c07
-- name    : P2M_Formalism_FourierDecayAlt_P_SignAntidiagonal_sg_val__ef8cc9865c07
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:30:57.330807+00:00
-- url     : https://prove2.me/theorems/79ae1d64-e3b1-5424-b3b9-48582cbaea1f
-- title:
--   P2 M Formalism Fourier Decay Alt P Sign Antidiagonal sg val  ef8cc9865c07: P2 M Formalism Fourier Decay Alt P Sign Antidiagonal sg val  ef8cc9865c07
-- statement:
--   The P2 M Formalism Fourier Decay Alt P Sign Antidiagonal sg val  ef8cc9865c07 construction uses the P2 M Formalism Fourier Decay Alt P Sign Antidiagonal sg val  ef8cc9865c07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L60-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianInsertionVectorOrthogonal.lean#L60-L60

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianInsertionVectorOrthogonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants
noncomputable section
variable {k : ℕ} (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)

theorem P2M_Formalism_FourierDecayAlt_P_SignAntidiagonal_sg_val__ef8cc9865c07 (q : Fin (2 * (m + 1) + k + 1)) : (NFOne.sg k (m + 1) q).val = 2 * (m + 1) + k - q.val := by sorry

alias «Formalism».«FourierDecayAlt».«P».«SignAntidiagonal».«sg_val'» := P2M_Formalism_FourierDecayAlt_P_SignAntidiagonal_sg_val__ef8cc9865c07
