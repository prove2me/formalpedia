-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_rightMarginal_pureDensity_toOperator
-- name    : QEC.Semantics.DensityOperator.rightMarginal_pureDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:51:17.635372+00:00
-- url     : https://prove2.me/theorems/d2d1bd20-bd6f-41b5-b6cf-b750f08713e5
-- title:
--   Density Operator: right Marginal pure Density to Operator
-- statement:
--   The right marginal of a pure tensor density is its finite coefficient Gram operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L288-L301
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L288-L301

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

theorem QEC.Semantics.DensityOperator.rightMarginal_pureDensity_toOperator {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    (rightMarginal (pureDensity psi hpsi)).toOperator =
      (rightAmplitude b psi).comp (LinearMap.adjoint (rightAmplitude b psi)) := by sorry
