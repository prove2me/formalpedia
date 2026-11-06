-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorPauliZ
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.conj_tensorPauliZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:23:38.209541+00:00
-- url     : https://prove2.me/theorems/f2301e63-72b3-40e0-b9a5-b86bf4baeca6
-- title:
--   Pauli Like Pair: conj tensor Pauli Z
-- statement:
--   The Pauli Like Pair construction uses the conj tensor Pauli Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L636-L643
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L636-L643

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

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.conj_tensorPauliZ :
    P.factorization.conjOperator P.tensorPauliZ = P.z := by sorry
