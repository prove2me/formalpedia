-- Prove2me | Theorems.Thm_QEC_Locality_tensorRight_adjoint_comp_factorSwap
-- name    : QEC.Locality.tensorRight_adjoint_comp_factorSwap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:31.694189+00:00
-- url     : https://prove2.me/theorems/cc0bdd7f-3b62-45f5-b04c-3e08fbac329f
-- title:
--   Locality: tensor Right adjoint comp factor Swap
-- statement:
--   The Locality construction uses the tensor Right adjoint comp factor Swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L252-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L252-L261

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.tensorRight_adjoint_comp_factorSwap (S : FiniteSubsystem ι)
    (h : Qubit.Bitstring S.SelectedCoordinates) :
    (LinearMap.adjoint
        (tensorRight S.complementSystem S.selectedSystem (ket h))).comp
      S.factorSwap.toLinearEquiv.toLinearMap =
      LinearMap.adjoint
        (tensorLeft S.selectedSystem S.complementSystem (ket h)) := by sorry
