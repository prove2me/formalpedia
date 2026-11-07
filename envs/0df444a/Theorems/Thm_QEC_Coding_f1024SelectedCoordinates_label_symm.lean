-- Prove2me | Theorems.Thm_QEC_Coding_f1024SelectedCoordinates_label_symm
-- name    : QEC.Coding.f1024SelectedCoordinates_label_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:15:39.484059+00:00
-- url     : https://prove2.me/theorems/391c1891-299f-423b-b582-651f982d0e12
-- title:
--   Coding: f1024 Selected Coordinates label symm
-- statement:
--   The selected coordinates of the inverse bitstring label recover its binary word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L80-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L80-L89

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.f1024SelectedCoordinates_label_symm
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    f1024SelectedCoordinates (why24ComputationalLabelEquiv.symm bits) =
      PauliSymplectic.bitstringWordEquiv (Fin 10) bits := by sorry
