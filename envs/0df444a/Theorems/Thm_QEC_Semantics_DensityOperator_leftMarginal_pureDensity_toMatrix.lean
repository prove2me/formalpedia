-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_leftMarginal_pureDensity_toMatrix
-- name    : QEC.Semantics.DensityOperator.leftMarginal_pureDensity_toMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:21:26.963003+00:00
-- url     : https://prove2.me/theorems/028c6a1f-ef29-4865-8bc1-982200744fc2
-- title:
--   Density Operator: left Marginal pure Density to Matrix
-- statement:
--   The left marginal matrix is the transpose of the other finite Gram matrix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L371-L390
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L371-L390

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

theorem QEC.Semantics.DensityOperator.leftMarginal_pureDensity_toMatrix {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (bH : OrthonormalBasis (Fin (Module.finrank Complex H)) Complex H)
    (bK : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    LinearMap.toMatrix bK.toBasis bK.toBasis
      (leftMarginal (pureDensity psi hpsi)).toOperator =
      ((coefficientMatrix bH bK psi).conjTranspose * coefficientMatrix bH bK psi).transpose := by sorry
