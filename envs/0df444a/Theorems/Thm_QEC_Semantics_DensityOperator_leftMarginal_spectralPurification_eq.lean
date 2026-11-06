-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_leftMarginal_spectralPurification_eq
-- name    : QEC.Semantics.DensityOperator.leftMarginal_spectralPurification_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:22:27.016663+00:00
-- url     : https://prove2.me/theorems/cdc51f50-83a6-4fee-85ca-7a5084c05394
-- title:
--   Density Operator: left Marginal spectral Purification eq
-- statement:
--   The concrete left marginal of the spectral purification is equal as a density operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L630-L632
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L630-L632

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

theorem QEC.Semantics.DensityOperator.leftMarginal_spectralPurification_eq (rho : DensityOperator H) :
    leftMarginal (spectralPurification rho) = rho := by sorry
