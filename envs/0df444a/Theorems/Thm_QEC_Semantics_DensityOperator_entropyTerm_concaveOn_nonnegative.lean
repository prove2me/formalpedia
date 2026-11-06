-- Prove2me | Theorems.Thm_QEC_Semantics_DensityOperator_entropyTerm_concaveOn_nonnegative
-- name    : QEC.Semantics.DensityOperator.entropyTerm_concaveOn_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:03.095081+00:00
-- url     : https://prove2.me/theorems/092313d2-051f-44ef-8566-fd36cf775ab4
-- title:
--   Density Operator: entropy Term concave On nonnegative
-- statement:
--   The base-two entropy contribution is concave on the nonnegative reals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L40-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/QuditBounds.lean#L40-L44

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

theorem QEC.Semantics.DensityOperator.entropyTerm_concaveOn_nonnegative :
    ConcaveOn Real (Set.Ici (0 : Real)) entropyTerm := by sorry
