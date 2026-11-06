-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_pureMarginals_balanced_charpoly
-- name    : QEC.Semantics.DensityOperator.pureMarginals_balanced_charpoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:21:30.011608+00:00
-- url     : https://prove2.me/theorems/39b57949-0fb7-4e44-afe7-85b6afdf3d47
-- title:
--   Density Operator: pure Marginals balanced charpoly
-- statement:
--   The two pure-state marginals have the same nonzero characteristic roots, with zeros explicit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L393-L426
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L393-L426

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

theorem QEC.Semantics.DensityOperator.pureMarginals_balanced_charpoly {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1) :
    (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex K) *
        (rightMarginal (pureDensity psi hpsi)).toOperator.charpoly =
      (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex H) *
        (leftMarginal (pureDensity psi hpsi)).toOperator.charpoly := by sorry
