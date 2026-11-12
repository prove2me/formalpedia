-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_reducedCombination_injective
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedCombination_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:35:11.495484+00:00
-- url     : https://prove2.me/theorems/bd880698-1369-40bd-aa6f-806d90f7438b
-- title:
--   Binary Row Family: reduced Combination injective
-- statement:
--   The Binary Row Family construction uses the reduced Combination injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L958-L966
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L958-L966

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.reducedCombination_injective
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal) :
    Function.Injective R.reducedCombination := by sorry
