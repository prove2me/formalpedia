-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_encodedObservable_operatorNorm_le_two
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.encodedObservable_operatorNorm_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:24:17.581657+00:00
-- url     : https://prove2.me/theorems/e79d92a9-8a64-4954-ad89-f57724b1dd9d
-- title:
--   Pauli Like Pair: encoded Observable operator Norm le two
-- statement:
--   CLBT's encoded observable has the required uniform operator-norm bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1198-L1205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1198-L1205

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

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.encodedObservable_operatorNorm_le_two
    (eta : DensityOperator Qubit.QubitSpace) :
    ‖LinearMap.toContinuousLinearMap (P.encodedObservable eta)‖ ≤ 2 := by sorry
