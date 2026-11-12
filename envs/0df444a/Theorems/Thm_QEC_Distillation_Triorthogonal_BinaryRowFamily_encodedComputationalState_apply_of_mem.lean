-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedComputationalState_apply_of_mem
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedComputationalState_apply_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:26:55.251428+00:00
-- url     : https://prove2.me/theorems/7ef2e6d9-1cdc-4d66-83cb-c2e6c4dedff7
-- title:
--   Binary Row Family: encoded Computational State apply of mem
-- statement:
--   A computational codeword has the uniform coset amplitude on its logical class.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1018-L1030
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1018-L1030

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open Coding Semantics
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe uR uM uI
universe u v w
variable {OddRow : Type u} {EvenRow : Type v} {Col : Type w}
variable [Fintype OddRow] [Fintype EvenRow] [Fintype Col]
variable [DecidableEq OddRow] [DecidableEq EvenRow] [DecidableEq Col]
open QEC.Distillation.Triorthogonal.BinaryRowFamily

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedComputationalState_apply_of_mem
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    (label : Qubit.Bitstring OddRow) {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∈ R.rowCode.dual.dual.carrier) :
    (R.encodedComputationalState hR label : Qubit.QubitRegister Col) bits =
      if label = (R.logicalBasisEquivLogicalQuotient hR).symm
          (Submodule.Quotient.mk ⟨bitstringWordEquiv Col bits, hbits⟩) then
        R.cssNormalizationScalar
      else
        0 := by sorry
