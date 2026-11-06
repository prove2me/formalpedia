-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_rightMarginal_pureDensity_toMatrix
-- name    : QEC.Semantics.DensityOperator.rightMarginal_pureDensity_toMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:21:24.724932+00:00
-- url     : https://prove2.me/theorems/0ee4ebac-545a-450f-9838-ea7f952b0910
-- title:
--   Density Operator: right Marginal pure Density to Matrix
-- statement:
--   The right marginal matrix is the ordinary left Gram matrix of the tensor coefficients.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L357-L368
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L357-L368

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

theorem QEC.Semantics.DensityOperator.rightMarginal_pureDensity_toMatrix {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (bH : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H)
    (bK : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    LinearMap.toMatrix bH.toBasis bH.toBasis
      (rightMarginal (pureDensity psi hpsi)).toOperator =
      coefficientMatrix bH bK psi * (coefficientMatrix bH bK psi).conjTranspose := by sorry
