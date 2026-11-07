-- Prove2me | Theorems.Thm_QEC_Coding_why24ComputationalLabelEquiv_coordinates
-- name    : QEC.Coding.why24ComputationalLabelEquiv_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:15:37.448501+00:00
-- url     : https://prove2.me/theorems/7c1c1894-7ccf-4c61-9662-76c8ffb73f1e
-- title:
--   Coding: why24 Computational Label Equiv coordinates
-- statement:
--   The bitstring image of an `F1024` label has exactly its selected coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L74-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L74-L77

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24ComputationalLabelEquiv_coordinates (β : F1024) :
    PauliSymplectic.bitstringWordEquiv (Fin 10) (why24ComputationalLabelEquiv β) =
      f1024SelectedCoordinates β := by sorry
