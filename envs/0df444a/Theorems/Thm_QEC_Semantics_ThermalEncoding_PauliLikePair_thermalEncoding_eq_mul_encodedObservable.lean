-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalEncoding_eq_mul_encodedObservable
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.thermalEncoding_eq_mul_encodedObservable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:59:38.606629+00:00
-- url     : https://prove2.me/theorems/d3ca1472-3f82-4b72-b061-ab3fe9762aa8
-- title:
--   Pauli Like Pair: thermal Encoding eq mul encoded Observable
-- statement:
--   The Pauli Like Pair construction uses the thermal Encoding eq mul encoded Observable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1260-L1267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1260-L1267

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

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.thermalEncoding_eq_mul_encodedObservable
    (sigma : DensityOperator P.AuxiliarySpace)
    (eta : DensityOperator Qubit.QubitSpace) :
    P.thermalEncoding sigma eta.toOperator =
      (P.thermalReferenceState sigma).toOperator * P.encodedObservable eta := by sorry
