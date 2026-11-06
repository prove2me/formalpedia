-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalDecoding_thermalEncoding_density
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.thermalDecoding_thermalEncoding_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:24:06.42363+00:00
-- url     : https://prove2.me/theorems/b7c79046-8f46-4211-8bb8-0fa3ca578a69
-- title:
--   Pauli Like Pair: thermal Decoding thermal Encoding density
-- statement:
--   The Pauli Like Pair construction uses the thermal Decoding thermal Encoding density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1140-L1144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1140-L1144

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

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.thermalDecoding_thermalEncoding_density
    (sigma : DensityOperator P.AuxiliarySpace) (eta : DensityOperator Qubit.QubitSpace) :
    P.thermalDecoding.mapDensity (P.thermalEncoding sigma |>.mapDensity eta) = eta := by sorry
