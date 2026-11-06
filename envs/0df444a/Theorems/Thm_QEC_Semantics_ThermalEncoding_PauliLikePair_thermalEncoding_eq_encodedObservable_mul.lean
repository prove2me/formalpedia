-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalEncoding_eq_encodedObservable_mul
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.thermalEncoding_eq_encodedObservable_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:24:08.021779+00:00
-- url     : https://prove2.me/theorems/e4777ea1-e29b-4345-b0af-afa1bd4d33cb
-- title:
--   Pauli Like Pair: thermal Encoding eq encoded Observable mul
-- statement:
--   The Pauli Like Pair construction uses the thermal Encoding eq encoded Observable mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1251-L1258
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1251-L1258

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

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.thermalEncoding_eq_encodedObservable_mul
    (sigma : DensityOperator P.AuxiliarySpace)
    (eta : DensityOperator Qubit.QubitSpace) :
    P.thermalEncoding sigma eta.toOperator =
      P.encodedObservable eta * (P.thermalReferenceState sigma).toOperator := by sorry
