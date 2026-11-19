-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15HInput_dephased_eq_diagonalAResource
-- name    : QEC.Distillation.BK15.Threshold.bk15HInput_dephased_eq_diagonalAResource
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:26:02.739705+00:00
-- url     : https://prove2.me/theorems/77fb4039-7682-4b24-8e05-481ff23b18c9
-- title:
--   Threshold: bk15 HInput dephased eq diagonal AResource
-- statement:
--   The same H input, after the real canonicalization, source-frame transport,
--   and dephasing route, is exactly the diagonal A resource used by the concrete
--   BK15 run.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L835-L848
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/Threshold.lean#L835-L848

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic

theorem QEC.Distillation.BK15.Threshold.bk15HInput_dephased_eq_diagonalAResource
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hleHalf : bk15HInputError rho <= 1 / 2) :
    hCanonicalizedDephasedInput rho =
      diagonalAResource (bk15HInputEpsilon rho hpositive hleHalf) := by sorry
