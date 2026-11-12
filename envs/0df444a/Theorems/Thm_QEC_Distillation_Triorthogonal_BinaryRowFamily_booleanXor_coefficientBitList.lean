-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_booleanXor_coefficientBitList
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.booleanXor_coefficientBitList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:35:53.778924+00:00
-- url     : https://prove2.me/theorems/7346be41-a3a8-40e3-923e-549a0c03f99e
-- title:
--   Binary Row Family: boolean Xor coefficient Bit List
-- statement:
--   The `B`-coordinate is the XOR of its physical-site matrix summands.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1027-L1034
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1027-L1034

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.booleanXor_coefficientBitList
    (R : BinaryRowFamily OddRow EvenRow Col) (f : Word (ZMod 2) Col)
    (r : Sum OddRow R.EvenBasisIndex) :
    booleanXor (R.coefficientBitList f r) = R.rowCoefficientMap f r := by sorry
