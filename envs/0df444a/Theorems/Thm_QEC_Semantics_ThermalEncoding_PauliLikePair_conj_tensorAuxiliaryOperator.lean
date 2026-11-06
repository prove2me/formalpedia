-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_conj_tensorAuxiliaryOperator
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.conj_tensorAuxiliaryOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:23:50.244636+00:00
-- url     : https://prove2.me/theorems/039592d5-a809-42e4-9e8d-638e6230cc5e
-- title:
--   Pauli Like Pair: conj tensor Auxiliary Operator
-- statement:
--   An operator commuting with both Pauli observables is `I_Q tensor A_aux` in
--   the factorization derived from those observables.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L705-L713
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L705-L713

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

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.conj_tensorAuxiliaryOperator
    (A : Operator H) (hX : Commute A P.x) (hZ : Commute A P.z) :
    P.factorization.conjOperator (P.tensorAuxiliaryOperator A hZ) = A := by sorry
