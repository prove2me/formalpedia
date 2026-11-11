-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCode_dual_dual_eq
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCode_dual_dual_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:38:42.936603+00:00
-- url     : https://prove2.me/theorems/081bf943-102a-4d08-9795-f79f40400a65
-- title:
--   Binary Row Family: row Code dual dual eq
-- statement:
--   The Binary Row Family construction uses the row Code dual dual eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2508-L2517
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2508-L2517

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCode_dual_dual_eq
    (R : BinaryRowFamily OddRow EvenRow Col) :
    R.rowCode.dual.dual.carrier = R.rowCode.carrier := by sorry
