-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedPlusState_inner_self
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedPlusState_inner_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T13:52:38.723256+00:00
-- url     : https://prove2.me/theorems/7b12124d-3160-4723-92f1-7556b556ef4f
-- title:
--   Binary Row Family: encoded Plus State inner self
-- statement:
--   The encoded logical equal superposition is explicitly normalized.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1244-L1248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1244-L1248

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Coding Semantics
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe uR uM uI
universe u v w
variable {OddRow : Type u} {EvenRow : Type v} {Col : Type w}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
open QEC.Distillation.Triorthogonal.BinaryRowFamily
attribute [-instance] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedPlusState_inner_self
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    inner Complex (R.encodedPlusState hR) (R.encodedPlusState hR) = 1 := by sorry
