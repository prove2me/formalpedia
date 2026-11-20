-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tTwirl_canonicalizedInput_eq_diagonalInput
-- name    : QEC.Distillation.BK05T.tTwirl_canonicalizedInput_eq_diagonalInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T19:07:21.078377+00:00
-- url     : https://prove2.me/theorems/c27578b8-d055-4542-9bc6-88876dce350a
-- title:
--   BK05 T: t Twirl canonicalized Input eq diagonal Input
-- statement:
--   The concrete finite-Clifford normalization followed by the actual
--   three-branch T twirl is exactly the source diagonal input at error
--   `1 - tFidelity rho ^ 2`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L614-L625
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L614-L625

import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic

theorem QEC.Distillation.BK05T.tTwirl_canonicalizedInput_eq_diagonalInput
    (rho : DensityOperator QubitSpace) :
    tTwirl (tCanonicalizedInput rho) =
      tDiagonalInput (bk05TFidelityError rho)
        (bk05TFidelityError_nonneg rho) (bk05TFidelityError_le_one rho) := by sorry
