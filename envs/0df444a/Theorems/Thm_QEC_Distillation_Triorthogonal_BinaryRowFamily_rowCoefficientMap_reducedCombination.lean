-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_reducedCombination
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:29:26.627857+00:00
-- url     : https://prove2.me/theorems/c2a8951e-8ba2-4f9e-9cda-0f623dbeb163
-- title:
--   Binary Row Family: row Coefficient Map reduced Combination
-- statement:
--   The Binary Row Family construction uses the row Coefficient Map reduced Combination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L975-L980
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L975-L980

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_reducedCombination
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) (Sum OddRow R.EvenBasisIndex)) :
    R.rowCoefficientMap (R.reducedCombination c) = c := by sorry
