-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedMagicState_inner_self
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedMagicState_inner_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T13:53:04.085954+00:00
-- url     : https://prove2.me/theorems/c0cda082-e433-440b-b693-a135b68c43fc
-- title:
--   Binary Row Family: encoded Magic State inner self
-- statement:
--   The encoded logical magic state is explicitly normalized.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1251-L1255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1251-L1255

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedMagicState_inner_self
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    inner Complex (R.encodedMagicState hR) (R.encodedMagicState hR) = 1 := by sorry
