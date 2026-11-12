-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_hammingWeight_reducedCombination_mod8
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.hammingWeight_reducedCombination_mod8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:37:14.404806+00:00
-- url     : https://prove2.me/theorems/652fbcd8-7918-4153-92ae-a025c3b75d49
-- title:
--   Binary Row Family: hamming Weight reduced Combination mod8
-- statement:
--   BH12 reduced-row weight polynomial modulo eight, with the cubic term eliminated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1373-L1380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L1373-L1380

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.hammingWeight_reducedCombination_mod8
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) (Sum OddRow R.EvenBasisIndex)) :
    (HammingWeight (R.reducedCombination c) : ZMod 8) =
      wordWeightSum8 (R.reducedWordList c) -
        2 * wordPairSum8 (R.reducedWordList c) := by sorry
