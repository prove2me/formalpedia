-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tDiagonalInput_toOperator_eq_blochProjector
-- name    : QEC.Distillation.BK05T.tDiagonalInput_toOperator_eq_blochProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:23:20.754085+00:00
-- url     : https://prove2.me/theorems/26b9bd4c-69c8-46b7-8ba4-0f972db89df1
-- title:
--   BK05 T: t Diagonal Input to Operator eq bloch Projector
-- statement:
--   The diagonal density has the advertised one-axis Bloch representation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L272-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L272-L283

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

theorem QEC.Distillation.BK05T.tDiagonalInput_toOperator_eq_blochProjector
    (epsilon : Real) (hzero : 0 ≤ epsilon) (hone : epsilon ≤ 1) :
    (tDiagonalInput epsilon hzero hone).toOperator =
      blochProjector (tDiagonalBloch epsilon) := by sorry
