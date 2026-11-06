-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_finrank_selectedSystem_eq_prod_selectedDimensions
-- name    : QEC.Semantics.QuditSubsystem.finrank_selectedSystem_eq_prod_selectedDimensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:07:16.639142+00:00
-- url     : https://prove2.me/theorems/5c67f829-b363-4695-a8a6-57218183f606
-- title:
--   Qudit Subsystem: finrank selected System eq prod selected Dimensions
-- statement:
--   The selected register dimension is the product of its concrete local dimensions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L162-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L162-L168

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
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι -> Nat}

theorem QEC.Semantics.QuditSubsystem.finrank_selectedSystem_eq_prod_selectedDimensions (S : QuditSubsystem q) :
    Module.finrank Complex S.selectedSystem = ∏ i ∈ S.selected, q i := by sorry
