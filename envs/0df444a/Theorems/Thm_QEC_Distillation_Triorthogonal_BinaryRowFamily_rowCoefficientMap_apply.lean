-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_apply
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:35:21.871211+00:00
-- url     : https://prove2.me/theorems/fa3f51a3-b94c-4a35-989f-a9fcfed85ad0
-- title:
--   Binary Row Family: row Coefficient Map apply
-- statement:
--   The left inverse is the finite matrix with entries `rowCoefficientEntry`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L989-L1018
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L989-L1018

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_apply
    (R : BinaryRowFamily OddRow EvenRow Col)
    (f : Word (ZMod 2) Col) (r : Sum OddRow R.EvenBasisIndex) :
    R.rowCoefficientMap f r =
      ∑ p, R.rowCoefficientEntry r p * f p := by sorry
