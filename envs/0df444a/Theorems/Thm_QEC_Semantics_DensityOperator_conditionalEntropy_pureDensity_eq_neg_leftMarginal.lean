-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_conditionalEntropy_pureDensity_eq_neg_leftMarginal
-- name    : QEC.Semantics.DensityOperator.conditionalEntropy_pureDensity_eq_neg_leftMarginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:47:36.804625+00:00
-- url     : https://prove2.me/theorems/34e2492a-57db-412a-a741-9b8ad8aeec12
-- title:
--   Density Operator: conditional Entropy pure Density eq neg left Marginal
-- statement:
--   A finite pure density has conditional entropy equal to minus either marginal entropy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L579-L585
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L579-L585

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

theorem QEC.Semantics.DensityOperator.conditionalEntropy_pureDensity_eq_neg_leftMarginal {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    conditionalEntropy (pureDensity psi hpsi) =
      - (leftMarginal (pureDensity psi hpsi)).vonNeumannEntropy := by sorry
