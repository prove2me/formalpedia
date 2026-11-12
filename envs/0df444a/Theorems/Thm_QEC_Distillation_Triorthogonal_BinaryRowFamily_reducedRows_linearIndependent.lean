-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_reducedRows_linearIndependent
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedRows_linearIndependent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:35:09.477267+00:00
-- url     : https://prove2.me/theorems/1b2fac44-35fa-4967-b6c0-4acb08a9413a
-- title:
--   Binary Row Family: reduced Rows linear Independent
-- statement:
--   The reduced rows are independent even when the supplied even rows are dependent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L932-L943
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L932-L943

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
variable {Index : Type u} [Fintype Index] [DecidableEq Index]
universe uO uE uC
open QEC.Distillation.Triorthogonal.BinaryRowFamily
variable {OddRow : Type uO} {EvenRow : Type uE} {Col : Type uC}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedRows_linearIndependent
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    LinearIndependent (ZMod 2) R.reducedRow := by sorry
