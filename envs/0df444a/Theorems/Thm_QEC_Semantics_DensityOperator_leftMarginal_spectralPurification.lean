-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_leftMarginal_spectralPurification
-- name    : QEC.Semantics.DensityOperator.leftMarginal_spectralPurification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:22:17.78128+00:00
-- url     : https://prove2.me/theorems/e506cdec-d1e4-460e-a8e3-3033571c84f4
-- title:
--   Density Operator: left Marginal spectral Purification
-- statement:
--   Tracing out the original factor of the spectral purification also recovers the input state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L619-L622
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L619-L622

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

theorem QEC.Semantics.DensityOperator.leftMarginal_spectralPurification (rho : DensityOperator H) :
    (leftMarginal (spectralPurification rho)).toOperator = rho.toOperator := by sorry
