-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_exists_reducedCombination_of_mem_rowCode
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.exists_reducedCombination_of_mem_rowCode
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:38:41.220787+00:00
-- url     : https://prove2.me/theorems/d4e8b7af-8a5a-4bdd-a673-ab0f220d7f10
-- title:
--   Binary Row Family: exists reduced Combination of mem row Code
-- statement:
--   The Binary Row Family construction uses the exists reduced Combination of mem row Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2493-L2501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2493-L2501

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.exists_reducedCombination_of_mem_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col)
    {f : Word (ZMod 2) Col} (hf : f ∈ R.rowCode.carrier) :
    ∃ c : Word (ZMod 2) R.ReducedRowIndex,
      R.reducedCombination c = f := by sorry
