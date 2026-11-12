-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedExponentInt_cast8_of_reducedCombination
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedExponentInt_cast8_of_reducedCombination
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:38:25.446352+00:00
-- url     : https://prove2.me/theorems/90f3367d-e6e4-4e22-9563-64480622e351
-- title:
--   Binary Row Family: corrected Exponent Int cast8 of reduced Combination
-- statement:
--   The Binary Row Family construction uses the corrected Exponent Int cast8 of reduced Combination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2424-L2438
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2424-L2438

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedExponentInt_cast8_of_reducedCombination
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (bits : Qubit.Bitstring Col)
    (c : Word (ZMod 2) R.ReducedRowIndex)
    (hbits : bitstringWordEquiv Col bits = R.reducedCombination c) :
    (R.correctedExponentInt bits : ZMod 8) =
      R.logicalExponent8 c R.reducedRowIndexList := by sorry
