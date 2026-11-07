-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_commute_of_commutes
-- name    : QEC.Coding.PauliSymplectic.toHermitianQubitOperator_commute_of_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:26:56.735193+00:00
-- url     : https://prove2.me/theorems/ac9e5211-aec3-4ab8-9e54-0e695f3177ff
-- title:
--   Pauli Symplectic: to Hermitian Qubit Operator commute of commutes
-- statement:
--   Binary symplectic commutation implies concrete commutation of the corrected
--   signed Hermitian operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/HermitianPauli.lean#L197-L211
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/HermitianPauli.lean#L197-L211

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Classical
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.toHermitianQubitOperator_commute_of_commutes
    (P Q : Binary ι) (h : Commutes P Q) :
    toHermitianQubitOperator P * toHermitianQubitOperator Q =
      toHermitianQubitOperator Q * toHermitianQubitOperator P := by sorry
