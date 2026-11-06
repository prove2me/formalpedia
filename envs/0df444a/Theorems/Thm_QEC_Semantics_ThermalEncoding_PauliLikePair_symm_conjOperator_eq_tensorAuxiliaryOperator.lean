-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_symm_conjOperator_eq_tensorAuxiliaryOperator
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.symm_conjOperator_eq_tensorAuxiliaryOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:59:27.565587+00:00
-- url     : https://prove2.me/theorems/729232cf-84dc-4fe4-87f6-5133c9f0910a
-- title:
--   Pauli Like Pair: symm conj Operator eq tensor Auxiliary Operator
-- statement:
--   Equivalent pulled-back Hamiltonian form used by the Gibbs calculation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L716-L720
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L716-L720

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

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.symm_conjOperator_eq_tensorAuxiliaryOperator
    (A : Operator H) (hX : Commute A P.x) (hZ : Commute A P.z) :
    P.factorization.symm.conjOperator A = P.tensorAuxiliaryOperator A hZ := by sorry
