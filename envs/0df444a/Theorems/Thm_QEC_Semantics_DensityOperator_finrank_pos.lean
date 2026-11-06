-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_finrank_pos
-- name    : QEC.Semantics.DensityOperator.finrank_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:17:58.899194+00:00
-- url     : https://prove2.me/theorems/5636d9b0-94a4-4d6a-9e83-734113b919fb
-- title:
--   Density Operator: finrank pos
-- statement:
--   A density operator can only live on a nonzero finite-dimensional system.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L88-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L88-L94

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.DensityOperator
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.DensityOperator.finrank_pos (rho : DensityOperator H) : 0 < Module.finrank Complex H := by sorry
