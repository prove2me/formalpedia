-- Prove2me | Theorems.Thm_QEC_Semantics_Qudit_log_finrank_quditRegister_eq_sum_log_dimensions
-- name    : QEC.Semantics.Qudit.log_finrank_quditRegister_eq_sum_log_dimensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:35.620069+00:00
-- url     : https://prove2.me/theorems/490b231c-f43a-4acb-bb51-00150991ab3b
-- title:
--   Qudit: log finrank qudit Register eq sum log dimensions
-- statement:
--   The base-two logarithm of a concrete register dimension is the sum of its
--   site-wise base-two logarithms.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L132-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L132-L140

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

theorem QEC.Semantics.Qudit.log_finrank_quditRegister_eq_sum_log_dimensions (q : ι -> Nat)
    (hq : forall i, 0 < q i) :
    Real.logb 2 (Module.finrank Complex (QuditRegister q) : Real) =
      ∑ i, Real.logb 2 (q i : Real) := by sorry
