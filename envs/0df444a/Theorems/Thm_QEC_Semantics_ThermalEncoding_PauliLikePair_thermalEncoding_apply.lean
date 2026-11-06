-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalEncoding_apply
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.thermalEncoding_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:54:33.031848+00:00
-- url     : https://prove2.me/theorems/d3dbbeee-1268-46dc-8440-dfb0ed2fd753
-- title:
--   Pauli Like Pair: thermal Encoding apply
-- statement:
--   The Pauli Like Pair construction uses the thermal Encoding apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1207-L1213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1207-L1213

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

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.thermalEncoding_apply
    (sigma : DensityOperator P.AuxiliarySpace) (A : Operator Qubit.QubitSpace) :
    P.thermalEncoding sigma A =
      P.factorization.conjOperator (TensorProduct.map A sigma.toOperator) := by sorry
