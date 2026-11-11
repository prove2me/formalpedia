-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedMagicState_apply_of_mem
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedMagicState_apply_of_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T13:52:17.343191+00:00
-- url     : https://prove2.me/theorems/d197d70b-38bb-415e-addd-b40a0cbd6bd4
-- title:
--   Binary Row Family: encoded Magic State apply of mem
-- statement:
--   The Binary Row Family construction uses the encoded Magic State apply of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1112-L1125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1112-L1125

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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedMagicState_apply_of_mem
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∈ R.rowCode.dual.dual.carrier) :
    (R.encodedMagicState hR : Qubit.QubitRegister Col) bits =
      R.cssNormalizationScalar *
        (logicalUniformScalar OddRow *
          piDivFourPhase ^ HammingWeight
            (bitstringWordEquiv OddRow
              ((R.logicalBasisEquivLogicalQuotient hR).symm
                (Submodule.Quotient.mk
                  ⟨bitstringWordEquiv Col bits, hbits⟩)))) := by sorry
