-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_rightMarginal_spectralPurification_eq
-- name    : QEC.Semantics.DensityOperator.rightMarginal_spectralPurification_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:51:54.485926+00:00
-- url     : https://prove2.me/theorems/5bbcec51-4e0e-4bd6-8c0d-3c8d60a9bd6b
-- title:
--   Density Operator: right Marginal spectral Purification eq
-- statement:
--   The concrete right marginal of the spectral purification is equal as a density operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L625-L627
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L625-L627

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

theorem QEC.Semantics.DensityOperator.rightMarginal_spectralPurification_eq (rho : DensityOperator H) :
    rightMarginal (spectralPurification rho) = rho := by sorry
