-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_quotient_mk_reducedCombination_eq_oddWordToLogicalQuotient
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.quotient_mk_reducedCombination_eq_oddWordToLogicalQuotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:38:40.650588+00:00
-- url     : https://prove2.me/theorems/6d6b035f-77cb-4f78-9ff4-0ea150a1160c
-- title:
--   Binary Row Family: quotient mk reduced Combination eq odd Word To Logical Quotient
-- statement:
--   A reduced word represents precisely the quotient class of its odd coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2562-L2575
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2562-L2575

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.quotient_mk_reducedCombination_eq_oddWordToLogicalQuotient
    (R : BinaryRowFamily OddRow EvenRow Col)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    Submodule.Quotient.mk
        (⟨R.reducedCombination c, R.reducedCombination_mem_dual_dual c⟩ :
          R.rowCode.dual.dual.carrier) =
      R.oddWordToLogicalQuotient (R.oddCoefficients c) := by sorry
