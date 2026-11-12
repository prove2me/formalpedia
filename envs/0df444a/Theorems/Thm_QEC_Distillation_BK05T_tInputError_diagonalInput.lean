-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tInputError_diagonalInput
-- name    : QEC.Distillation.BK05T.tInputError_diagonalInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:31:06.118203+00:00
-- url     : https://prove2.me/theorems/1382419e-11fd-4a76-ab23-9cdf9c22357d
-- title:
--   BK05 T: t Input Error diagonal Input
-- statement:
--   The diagonal error parameter is exactly epsilon.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L286-L290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L286-L290

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators

theorem QEC.Distillation.BK05T.tInputError_diagonalInput
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    tInputError (tDiagonalInput epsilon hzero hone) = epsilon := by sorry
