-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
-- name    : QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:45:14.420725+00:00
-- url     : https://prove2.me/theorems/1c8f9a30-a90c-425e-bdbd-0fc13fde4b33
-- title:
--   Pauli Symplectic: binary Pauli Kraus Family operator
-- statement:
--   The Pauli Symplectic construction uses the binary Pauli Kraus Family operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Correctability.lean#L31-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Correctability.lean#L31-L35

import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Correctability
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open scoped ComplexConjugate
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator {α : Type v} [Fintype α]
    (E : α → Binary ι) (amp : α → Complex) (a : α) :
    (binaryPauliKrausFamily E amp).operator a = amp a • toQubitOperator (E a) := by sorry
