-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedDimensions_positive_of_density
-- name    : QEC.Semantics.QuditSubsystem.selectedDimensions_positive_of_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:53.384643+00:00
-- url     : https://prove2.me/theorems/c756c198-0169-492f-b8e6-1295f984dd47
-- title:
--   Qudit Subsystem: selected Dimensions positive of density
-- statement:
--   Existence of a selected-system density operator forces all selected local dimensions positive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L171-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L171-L179

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

theorem QEC.Semantics.QuditSubsystem.selectedDimensions_positive_of_density (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    forall i, i ∈ S.selected -> 0 < q i := by sorry
