-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
-- name    : QEC.Semantics.DensityOperator.ext_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:35:11.042198+00:00
-- url     : https://prove2.me/theorems/ebffc5af-0445-4d72-9280-1aa9c1368bd0
-- title:
--   Density Operator: ext to Operator
-- statement:
--   Density operators are determined by their underlying linear operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L162-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/Purification.lean#L162-L167

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

theorem QEC.Semantics.DensityOperator.ext_toOperator {rho sigma : DensityOperator H}
    (h : rho.toOperator = sigma.toOperator) : rho = sigma := by sorry
