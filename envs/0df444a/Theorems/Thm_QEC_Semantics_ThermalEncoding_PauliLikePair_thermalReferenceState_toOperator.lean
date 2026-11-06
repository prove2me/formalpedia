-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_PauliLikePair_thermalReferenceState_toOperator
-- name    : QEC.Semantics.ThermalEncoding.PauliLikePair.thermalReferenceState_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:54:14.846671+00:00
-- url     : https://prove2.me/theorems/b0fbbe22-dcef-41f6-a201-5e0c459a4390
-- title:
--   Pauli Like Pair: thermal Reference State to Operator
-- statement:
--   The Pauli Like Pair construction uses the thermal Reference State to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1215-L1221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L1215-L1221

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

theorem QEC.Semantics.ThermalEncoding.PauliLikePair.thermalReferenceState_toOperator
    (sigma : DensityOperator P.AuxiliarySpace) :
    (P.thermalReferenceState sigma).toOperator =
      P.factorization.conjOperator
        (TensorProduct.map ((2 : Complex)⁻¹ • (1 : Operator Qubit.QubitSpace))
          sigma.toOperator) := by sorry
