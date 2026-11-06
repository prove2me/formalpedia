-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_conditionalEntropy_spectralPurification
-- name    : QEC.Semantics.DensityOperator.conditionalEntropy_spectralPurification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:57:54.846983+00:00
-- url     : https://prove2.me/theorems/739adca5-7c92-473e-886b-fe3d3bb13c75
-- title:
--   Density Operator: conditional Entropy spectral Purification
-- statement:
--   The spectral purification supplies the exact conditional-entropy identity used downstream.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L635-L641
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L635-L641

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

theorem QEC.Semantics.DensityOperator.conditionalEntropy_spectralPurification (rho : DensityOperator H) :
    conditionalEntropy (spectralPurification rho) = -rho.vonNeumannEntropy := by sorry
