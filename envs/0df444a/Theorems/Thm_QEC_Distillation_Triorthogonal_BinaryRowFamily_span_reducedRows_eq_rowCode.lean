-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_span_reducedRows_eq_rowCode
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.span_reducedRows_eq_rowCode
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:38:43.738827+00:00
-- url     : https://prove2.me/theorems/d8f62209-604d-47fd-9721-ed627c25b417
-- title:
--   Binary Row Family: span reduced Rows eq row Code
-- statement:
--   The independent reduced rows span exactly the original total row code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2465-L2485
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2465-L2485

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.span_reducedRows_eq_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col) :
    Submodule.span (ZMod 2) (Set.range R.reducedRow) = R.rowCode.carrier := by sorry
