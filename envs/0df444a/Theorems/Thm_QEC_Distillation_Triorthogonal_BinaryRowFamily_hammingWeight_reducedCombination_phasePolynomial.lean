-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_hammingWeight_reducedCombination_phasePolynomial
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.hammingWeight_reducedCombination_phasePolynomial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:38:37.147814+00:00
-- url     : https://prove2.me/theorems/679e1744-f622-47b3-b82f-c42125ae2c85
-- title:
--   Binary Row Family: hamming Weight reduced Combination phase Polynomial
-- statement:
--   The exact reduced weight is a logical term plus a degree-two Clifford exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1573-L1587
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1573-L1587

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.hammingWeight_reducedCombination_phasePolynomial
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    (HammingWeight (R.reducedCombination c) : ZMod 8) =
      R.logicalExponent8 c R.reducedRowIndexList + R.rowCliffordExponent8 c := by sorry
