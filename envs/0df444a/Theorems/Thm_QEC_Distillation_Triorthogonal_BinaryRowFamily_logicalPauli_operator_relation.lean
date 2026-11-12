-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPauli_operator_relation
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPauli_operator_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:08:00.039828+00:00
-- url     : https://prove2.me/theorems/e289c7ea-52ab-4e4d-8516-a244ec58d1da
-- title:
--   Binary Row Family: logical Pauli operator relation
-- statement:
--   Concrete logical Pauli operators obey `X_a Z_b = (-1)^(δ_ab) Z_b X_a`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L977-L997
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L977-L997

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPauli_operator_relation
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (a b : OddRow) :
    PauliSymplectic.toQubitOperator (R.logicalXPauli a) *
        PauliSymplectic.toQubitOperator (R.logicalZPauli b) =
      if a = b then
        -(PauliSymplectic.toQubitOperator (R.logicalZPauli b) *
          PauliSymplectic.toQubitOperator (R.logicalXPauli a))
      else
        PauliSymplectic.toQubitOperator (R.logicalZPauli b) *
          PauliSymplectic.toQubitOperator (R.logicalXPauli a) := by sorry
