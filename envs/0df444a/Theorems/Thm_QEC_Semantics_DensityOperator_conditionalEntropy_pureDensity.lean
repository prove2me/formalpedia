-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_conditionalEntropy_pureDensity
-- name    : QEC.Semantics.DensityOperator.conditionalEntropy_pureDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:51:58.487211+00:00
-- url     : https://prove2.me/theorems/3ea645b9-64f7-4797-ae88-8cc0ba012e6c
-- title:
--   Density Operator: conditional Entropy pure Density
-- statement:
--   A finite pure density has conditional entropy equal to minus its right marginal entropy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L569-L576
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L569-L576

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

theorem QEC.Semantics.DensityOperator.conditionalEntropy_pureDensity {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    conditionalEntropy (pureDensity psi hpsi) =
      - (rightMarginal (pureDensity psi hpsi)).vonNeumannEntropy := by sorry
