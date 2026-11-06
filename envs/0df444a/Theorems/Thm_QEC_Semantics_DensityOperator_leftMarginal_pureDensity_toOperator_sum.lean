-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_leftMarginal_pureDensity_toOperator_sum
-- name    : QEC.Semantics.DensityOperator.leftMarginal_pureDensity_toOperator_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:51:47.866495+00:00
-- url     : https://prove2.me/theorems/5fe7168f-e72d-4070-bbdb-d3ffdfcdafcb
-- title:
--   Density Operator: left Marginal pure Density to Operator sum
-- statement:
--   The left marginal of a pure tensor density, expanded in right tensor coefficients.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L304-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L304-L319

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

theorem QEC.Semantics.DensityOperator.leftMarginal_pureDensity_toOperator_sum {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    (leftMarginal (pureDensity psi hpsi)).toOperator =
      ∑ i, ∑ j,
        (inner Complex (rightTensorCoefficients b psi j) (rightTensorCoefficients b psi i)) •
          (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap := by sorry
