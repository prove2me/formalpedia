-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorPauliX
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.conj_tensorPauliX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:23:37.24887+00:00
-- url     : https://prove2.me/theorems/79905721-6f00-4782-b5b8-6b47ace730f2
-- title:
--   Pauli Like Pair: conj tensor Pauli X
-- statement:
--   The Pauli Like Pair construction uses the conj tensor Pauli X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L627-L634
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L627-L634

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.ThermalEncoding.PauliLikePair
variable (P : PauliLikePair H)

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.conj_tensorPauliX :
    P.factorization.conjOperator P.tensorPauliX = P.x := by sorry
