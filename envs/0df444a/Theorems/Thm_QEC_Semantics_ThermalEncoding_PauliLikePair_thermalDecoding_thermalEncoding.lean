-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalDecoding_thermalEncoding
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.thermalDecoding_thermalEncoding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:23:58.311666+00:00
-- url     : https://prove2.me/theorems/5fc4522a-f0a5-40a8-9e24-b0202ba44978
-- title:
--   Pauli Like Pair: thermal Decoding thermal Encoding
-- statement:
--   The Pauli Like Pair construction uses the thermal Decoding thermal Encoding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1130-L1138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1130-L1138

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
set_option maxRecDepth 4096

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.thermalDecoding_thermalEncoding
    (sigma : DensityOperator P.AuxiliarySpace) (A : Operator Qubit.QubitSpace) :
    P.thermalDecoding (P.thermalEncoding sigma A) = A := by sorry
