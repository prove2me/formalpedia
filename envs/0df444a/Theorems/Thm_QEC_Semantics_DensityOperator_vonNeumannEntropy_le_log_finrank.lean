-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_le_log_finrank
-- name    : QEC.Semantics.DensityOperator.vonNeumannEntropy_le_log_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:06:38.319321+00:00
-- url     : https://prove2.me/theorems/91fedf26-938f-4757-a9fe-f46901cacd37
-- title:
--   Density Operator: von Neumann Entropy le log finrank
-- statement:
--   Spectral maximum entropy for every finite-dimensional density operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L97-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L97-L102

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

theorem QEC.Semantics.DensityOperator.vonNeumannEntropy_le_log_finrank (rho : DensityOperator H) :
    rho.vonNeumannEntropy <= Real.logb 2 (Module.finrank Complex H : Real) := by sorry
