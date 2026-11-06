-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_sum_rightTensorCoefficients_tmul
-- name    : QEC.Semantics.DensityOperator.sum_rightTensorCoefficients_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:36:58.790058+00:00
-- url     : https://prove2.me/theorems/ea1ddc24-a631-4c7a-a652-37b74d462d3c
-- title:
--   Density Operator: sum right Tensor Coefficients tmul
-- statement:
--   Re-expanding the finite right coefficients reconstructs the original tensor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L237-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L237-L257

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

theorem QEC.Semantics.DensityOperator.sum_rightTensorCoefficients_tmul {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) :
    ∑ j, rightTensorCoefficients b psi j ⊗ₜ[Complex] b j = psi := by sorry
