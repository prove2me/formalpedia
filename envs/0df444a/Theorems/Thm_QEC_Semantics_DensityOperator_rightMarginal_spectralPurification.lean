-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_rightMarginal_spectralPurification
-- name    : QEC.Semantics.DensityOperator.rightMarginal_spectralPurification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:37:52.911319+00:00
-- url     : https://prove2.me/theorems/d98ba46a-2751-419e-b3e9-2ec0f2676927
-- title:
--   Density Operator: right Marginal spectral Purification
-- statement:
--   Tracing out the reference of the explicit spectral purification recovers the input state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L589-L602
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L589-L602

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.rightMarginal_spectralPurification (rho : DensityOperator H) :
    (rightMarginal (spectralPurification rho)).toOperator = rho.toOperator := by sorry
