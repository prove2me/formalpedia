-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_pureDensity_balanced_charpoly
-- name    : QEC.Semantics.DensityOperator.pureDensity_balanced_charpoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:21:58.285259+00:00
-- url     : https://prove2.me/theorems/8887274e-1f4e-4291-8581-0b1158c95e99
-- title:
--   Density Operator: pure Density balanced charpoly
-- statement:
--   The characteristic polynomial of a normalized rank-one density has one root at one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L514-L535
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L514-L535

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

theorem QEC.Semantics.DensityOperator.pureDensity_balanced_charpoly (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    (Polynomial.X : Polynomial Complex) * (pureDensity psi hpsi).toOperator.charpoly =
      (Polynomial.X : Polynomial Complex) ^ (Module.finrank Complex H) *
        (Polynomial.X - 1) := by sorry
