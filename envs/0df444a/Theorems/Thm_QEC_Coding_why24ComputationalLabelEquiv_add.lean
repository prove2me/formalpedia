-- Prove2me | Theorems.Thm_QEC_Coding_why24ComputationalLabelEquiv_add
-- name    : QEC.Coding.why24ComputationalLabelEquiv_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:48.386146+00:00
-- url     : https://prove2.me/theorems/05da79b4-d890-4419-aff0-96ec2a61bc19
-- title:
--   Coding: why24 Computational Label Equiv add
-- statement:
--   Source-exact label action of a field shift on the ten-qubit bitstring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L141-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L141-L163

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.why24ComputationalLabelEquiv_add (β : F1024)
    (bits : Semantics.Qubit.Bitstring (Fin 10)) :
    why24ComputationalLabelEquiv (why24ComputationalLabelEquiv.symm bits + β) =
      Semantics.Qubit.flipSupport (PauliSymplectic.binarySupport (f1024SelectedCoordinates β))
        bits := by sorry
