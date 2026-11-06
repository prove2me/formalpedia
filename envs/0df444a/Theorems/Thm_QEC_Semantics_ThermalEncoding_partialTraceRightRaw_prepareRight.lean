-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_partialTraceRightRaw_prepareRight
-- name    : QEC.Semantics.ThermalEncoding.partialTraceRightRaw_prepareRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:23:52.163006+00:00
-- url     : https://prove2.me/theorems/0ef23663-f7f5-4699-a015-9c00161d1684
-- title:
--   Thermal Encoding: partial Trace Right Raw prepare Right
-- statement:
--   Tracing out the prepared factor returns the original operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L887-L914
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L887-L914

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
variable {K : Type}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.ThermalEncoding.partialTraceRightRaw_prepareRight (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (A : Operator H) :
    partialTraceRightRaw H K (prepareRight H K sigma A) = A := by sorry
