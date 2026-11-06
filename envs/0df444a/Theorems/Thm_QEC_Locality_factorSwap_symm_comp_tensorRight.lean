-- Prove2me | Theorems.Thm_QEC_Locality_factorSwap_symm_comp_tensorRight
-- name    : QEC.Locality.factorSwap_symm_comp_tensorRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:14.428893+00:00
-- url     : https://prove2.me/theorems/ad62ba73-dd86-443b-ab0a-1df8d1e94b13
-- title:
--   Locality: factor Swap symm comp tensor Right
-- statement:
--   The Locality construction uses the factor Swap symm comp tensor Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L243-L250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L243-L250

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

theorem QEC.Locality.factorSwap_symm_comp_tensorRight (S : FiniteSubsystem ι)
    (h : Qubit.Bitstring S.SelectedCoordinates) :
    S.factorSwap.symm.toLinearEquiv.toLinearMap.comp
      (tensorRight S.complementSystem S.selectedSystem (ket h)) =
      tensorLeft S.selectedSystem S.complementSystem (ket h) := by sorry
