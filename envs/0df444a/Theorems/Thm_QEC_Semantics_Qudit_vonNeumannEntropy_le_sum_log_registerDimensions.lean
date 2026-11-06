-- Prove2me | Theorems.Thm_QEC_Semantics_Qudit_vonNeumannEntropy_le_sum_log_registerDimensions
-- name    : QEC.Semantics.Qudit.vonNeumannEntropy_le_sum_log_registerDimensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:36.159746+00:00
-- url     : https://prove2.me/theorems/432b22f2-b8ae-40aa-b151-efff19096eca
-- title:
--   Qudit: von Neumann Entropy le sum log register Dimensions
-- statement:
--   Maximum entropy on a concrete finite-qudit register is bounded by its
--   heterogeneous local-dimension logarithm sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L144-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L144-L152

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
open QEC.Semantics.Qudit
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.Qudit.vonNeumannEntropy_le_sum_log_registerDimensions (q : ι -> Nat)
    (rho : DensityOperator (QuditRegister q)) :
    rho.vonNeumannEntropy <= ∑ i, Real.logb 2 (q i : Real) := by sorry
