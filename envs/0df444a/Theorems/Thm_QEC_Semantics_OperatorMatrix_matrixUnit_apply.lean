-- Prove2me | Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
-- name    : QEC.Semantics.OperatorMatrix.matrixUnit_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:53:58.233803+00:00
-- url     : https://prove2.me/theorems/7c8d44ea-cc15-4d60-af80-ca92e9aeb3ed
-- title:
--   Operator Matrix: matrix Unit apply
-- statement:
--   The Operator Matrix construction uses the matrix Unit apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Choi.lean#L29-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Choi.lean#L29-L31

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Choi
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
open QEC.Semantics.OperatorMatrix
variable {n : Nat} {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.OperatorMatrix.matrixUnit_apply (b : OrthonormalBasis (Fin n) Complex H) (i j : Fin n) (x : H) :
    matrixUnit b i j x = inner Complex (b j) x • b i := by sorry

attribute [defeq] QEC.Semantics.OperatorMatrix.matrixUnit_apply
