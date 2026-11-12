-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedPlusState_apply_of_mem
-- name    : QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedPlusState_apply_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:09:29.024121+00:00
-- url     : https://prove2.me/theorems/5171aca2-be55-4db2-80d4-877d565b074e
-- title:
--   Binary Row Family: encoded Plus State apply of mem
-- statement:
--   The Binary Row Family construction uses the encoded Plus State apply of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1072-L1079
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/CSS.lean#L1072-L1079

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_Triorthogonal_CSS
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

theorem QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedPlusState_apply_of_mem
    (R : BinaryRowFamily OddRow EvenRow Col) (hR : R.IsTriorthogonal)
    {bits : Qubit.Bitstring Col}
    (hbits : bitstringWordEquiv Col bits ∈ R.rowCode.dual.dual.carrier) :
    (R.encodedPlusState hR : Qubit.QubitRegister Col) bits =
      R.cssNormalizationScalar * logicalUniformScalar OddRow := by sorry
