-- Prove2me | Theorems.Thm_QEC_Semantics_Qudit_finrank_quditRegister_eq_prod_dimensions
-- name    : QEC.Semantics.Qudit.finrank_quditRegister_eq_prod_dimensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:07:13.286474+00:00
-- url     : https://prove2.me/theorems/2523853e-f74f-41e3-9c72-65b129af1360
-- title:
--   Qudit: finrank qudit Register eq prod dimensions
-- statement:
--   The dimension of a concrete finite-qudit register is the product of its
--   site-wise local dimensions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L112-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L112-L116

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

theorem QEC.Semantics.Qudit.finrank_quditRegister_eq_prod_dimensions (q : ι -> Nat) :
    Module.finrank Complex (QuditRegister q) = ∏ i, q i := by sorry
