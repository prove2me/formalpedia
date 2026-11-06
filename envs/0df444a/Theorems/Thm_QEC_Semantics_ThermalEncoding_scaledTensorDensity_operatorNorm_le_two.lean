-- Prove2me | Theorems.Thm_QEC_Semantics_ThermalEncoding_scaledTensorDensity_operatorNorm_le_two
-- name    : QEC.Semantics.ThermalEncoding.scaledTensorDensity_operatorNorm_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:23:23.570916+00:00
-- url     : https://prove2.me/theorems/021ecafb-91bd-4cf6-b242-3e51552926f4
-- title:
--   Thermal Encoding: scaled Tensor Density operator Norm le two
-- statement:
--   Twice a density operator, tensored with an identity, has norm at most two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L205-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ThermalEncoding.lean#L205-L229

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

theorem QEC.Semantics.ThermalEncoding.scaledTensorDensity_operatorNorm_le_two {K : Type}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator H) :
    ‖LinearMap.toContinuousLinearMap
      (TensorProduct.map ((2 : Complex) • rho.toOperator)
        (1 : Operator K))‖ ≤ 2 := by sorry
