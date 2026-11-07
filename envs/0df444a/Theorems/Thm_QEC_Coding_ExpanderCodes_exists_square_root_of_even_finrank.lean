-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_exists_square_root_of_even_finrank
-- name    : QEC.Coding.ExpanderCodes.exists_square_root_of_even_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:45:21.247149+00:00
-- url     : https://prove2.me/theorems/8841d37f-63d3-46ef-8929-ce9e8d7ace97
-- title:
--   Expander Codes: exists square root of even finrank
-- statement:
--   A nonsquare constant acquires a square root in every even-degree finite extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldQuadraticSplitting.lean#L20-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldQuadraticSplitting.lean#L20-L37

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSpecialization
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open scoped QuadraticAlgebra

theorem QEC.Coding.ExpanderCodes.exists_square_root_of_even_finrank
    {F K : Type*} [Field F] [Field K] [Finite K] [Algebra F K]
    (epsilon : F) (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon)
    (hEven : 2 ∣ Module.finrank F K) :
    ∃ r : K, r ^ 2 = algebraMap F K epsilon := by sorry
