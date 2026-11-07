-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_exists_constant_square_root_of_even_finrank
-- name    : QEC.Coding.ExpanderCodes.exists_constant_square_root_of_even_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:46:36.284678+00:00
-- url     : https://prove2.me/theorems/4378d593-cc57-4993-b336-8307d6ed3291
-- title:
--   Expander Codes: exists constant square root of even finrank
-- statement:
--   Every constant becomes a square in an even-degree finite-field extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldSquareParameters.lean#L113-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldSquareParameters.lean#L113-L122

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
import Mathlib.GroupTheory.Coset.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Linarith
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSquareParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open IntermediateField

theorem QEC.Coding.ExpanderCodes.exists_constant_square_root_of_even_finrank
    {F K : Type*} [Field F] [Field K] [Finite K] [Algebra F K]
    (a : F) (hEven : 2 ∣ Module.finrank F K) :
    ∃ r : K, r ^ 2 = algebraMap F K a := by sorry
