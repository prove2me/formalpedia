-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tInputSquaredOverlap_diagonalInput
-- name    : QEC.Distillation.BK05T.tInputSquaredOverlap_diagonalInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:23:01.155252+00:00
-- url     : https://prove2.me/theorems/d0439a85-0db5-4dbf-ba3d-8f7bcb7fd52f
-- title:
--   BK05 T: t Input Squared Overlap diagonal Input
-- statement:
--   The diagonal mixture uses exactly epsilon as its squared-overlap error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L193-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L193-L203

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

theorem QEC.Distillation.BK05T.tInputSquaredOverlap_diagonalInput
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    tInputSquaredOverlap (tDiagonalInput epsilon hzero hone) = 1 - epsilon := by sorry
