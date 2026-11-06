-- Prove2me | Theorems.Thm_QEC_Semantics_Qudit_dimensions_positive_of_density
-- name    : QEC.Semantics.Qudit.dimensions_positive_of_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:34.878486+00:00
-- url     : https://prove2.me/theorems/40e88d8d-42ce-41f9-9b6c-a846e39ffc03
-- title:
--   Qudit: dimensions positive of density
-- statement:
--   Existence of a density operator on a concrete register forces every local
--   dimension in that register to be positive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L120-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L120-L128

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

theorem QEC.Semantics.Qudit.dimensions_positive_of_density (q : ι -> Nat)
    (rho : DensityOperator (QuditRegister q)) :
    forall i, 0 < q i := by sorry
