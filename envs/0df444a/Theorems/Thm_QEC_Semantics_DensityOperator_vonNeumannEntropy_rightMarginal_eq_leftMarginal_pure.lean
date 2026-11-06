-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:38:19.506801+00:00
-- url     : https://prove2.me/theorems/bf83c830-0943-4b75-9143-a33d84f71fc0
-- title:
--   Density Operator: von Neumann Entropy right Marginal eq left Marginal pure
-- statement:
--   Every finite pure bipartite density has equal base-two entropy on its two marginals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L459-L467
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L459-L467

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

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    (rightMarginal (pureDensity psi hpsi)).vonNeumannEntropy =
      (leftMarginal (pureDensity psi hpsi)).vonNeumannEntropy := by sorry
