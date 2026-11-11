-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_range_reducedCombination_eq_rowCode
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.range_reducedCombination_eq_rowCode
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:38:51.871841+00:00
-- url     : https://prove2.me/theorems/d15e7a7a-b6d9-43c6-9c0d-08ab1582a46e
-- title:
--   Binary Row Family: range reduced Combination eq row Code
-- statement:
--   The Binary Row Family construction uses the range reduced Combination eq row Code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2487-L2491
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2487-L2491

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.range_reducedCombination_eq_rowCode
    (R : BinaryRowFamily OddRow EvenRow Col) :
    LinearMap.range R.reducedCombination = R.rowCode.carrier := by sorry
