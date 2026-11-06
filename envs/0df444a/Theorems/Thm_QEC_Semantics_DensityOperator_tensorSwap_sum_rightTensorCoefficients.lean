-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_tensorSwap_sum_rightTensorCoefficients
-- name    : QEC.Semantics.DensityOperator.tensorSwap_sum_rightTensorCoefficients
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:20:59.84442+00:00
-- url     : https://prove2.me/theorems/90dee527-3dd4-4e8f-a50c-3dc0fdeec211
-- title:
--   Density Operator: tensor Swap sum right Tensor Coefficients
-- statement:
--   Swapping a tensor swaps the two factors in its finite right-coefficient expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L260-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L260-L269

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

theorem QEC.Semantics.DensityOperator.tensorSwap_sum_rightTensorCoefficients {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) :
    tensorSwap H K psi = ∑ j, b j ⊗ₜ[Complex] rightTensorCoefficients b psi j := by sorry
