-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalExponent8_eq_hammingWeight_oddCoefficients
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalExponent8_eq_hammingWeight_oddCoefficients
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:39:51.149179+00:00
-- url     : https://prove2.me/theorems/04297122-fcd3-464c-b386-05242486d0b6
-- title:
--   Binary Row Family: logical Exponent8 eq hamming Weight odd Coefficients
-- statement:
--   The residual logical exponent is the Hamming weight of the odd coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2597-L2610
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2597-L2610

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalExponent8_eq_hammingWeight_oddCoefficients
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    R.logicalExponent8 c R.reducedRowIndexList =
      (HammingWeight (R.oddCoefficients c) : ZMod 8) := by sorry
