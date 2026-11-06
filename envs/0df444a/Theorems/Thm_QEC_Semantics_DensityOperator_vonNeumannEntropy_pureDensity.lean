-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_pureDensity
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_pureDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:21:55.450174+00:00
-- url     : https://prove2.me/theorems/e621b900-ea54-4dbd-b055-8b4e8c5814c0
-- title:
--   Density Operator: von Neumann Entropy pure Density
-- statement:
--   A normalized finite rank-one density has zero base-two von Neumann entropy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L538-L560
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L538-L560

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

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_pureDensity (psi : H) (hpsi : ‖psi‖ ^ 2 = 1) :
    (pureDensity psi hpsi).vonNeumannEntropy = 0 := by sorry
