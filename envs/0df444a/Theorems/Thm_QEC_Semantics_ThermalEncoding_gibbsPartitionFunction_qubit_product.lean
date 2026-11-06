-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_gibbsPartitionFunction_qubit_product
-- name    : QEC.Semantics.ThermalEncoding.gibbsPartitionFunction_qubit_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:23:20.169191+00:00
-- url     : https://prove2.me/theorems/fc5e710a-6220-4da8-b610-8f4fb9612b19
-- title:
--   Thermal Encoding: gibbs Partition Function qubit product
-- statement:
--   The Thermal Encoding construction uses the gibbs Partition Function qubit product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L294-L300
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L294-L300

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

theorem QEC.Semantics.ThermalEncoding.gibbsPartitionFunction_qubit_product {ι : Type} [Fintype ι]
    (beta : Real) (energy : ι → Real) :
    gibbsPartitionFunction beta (fun qi : Fin 2 × ι => energy qi.2) =
      2 * gibbsPartitionFunction beta energy := by sorry
