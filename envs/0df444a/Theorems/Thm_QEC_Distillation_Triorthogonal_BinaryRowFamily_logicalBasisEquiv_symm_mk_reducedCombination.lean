-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalBasisEquiv_symm_mk_reducedCombination
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalBasisEquiv_symm_mk_reducedCombination
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:38:57.885763+00:00
-- url     : https://prove2.me/theorems/953c474f-9bf1-4c12-bd7a-3d4df134d7b8
-- title:
--   Binary Row Family: logical Basis Equiv symm mk reduced Combination
-- statement:
--   The Binary Row Family construction uses the logical Basis Equiv symm mk reduced Combination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2583-L2594
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Transversal.lean#L2583-L2594

import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalBasisEquiv_symm_mk_reducedCombination
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (c : Word (ZMod 2) R.ReducedRowIndex) :
    (R.logicalBasisEquivLogicalQuotient hR).symm
        (Submodule.Quotient.mk
          (⟨R.reducedCombination c, R.reducedCombination_mem_dual_dual c⟩ :
            R.rowCode.dual.dual.carrier)) =
      R.reducedLogicalBits c := by sorry
