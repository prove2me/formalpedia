-- Prove2me | Theorems.Thm_QEC_Coding_ExpanderCodes_exists_split_full_degree_parameter
-- name    : QEC.Coding.ExpanderCodes.exists_split_full_degree_parameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:45:21.438376+00:00
-- url     : https://prove2.me/theorems/fd10d893-5923-423e-abb2-d9b304d9ce1a
-- title:
--   Expander Codes: exists split full degree parameter
-- statement:
--   Actual even-degree specializations simultaneously provide a nonzero
--   square root of the constant parameter and an irreducible full-degree point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldQuadraticSplitting.lean#L41-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FiniteFieldQuadraticSplitting.lean#L41-L59

import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldSpecialization
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FiniteFieldQuadraticSplitting
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes
open scoped QuadraticAlgebra

theorem QEC.Coding.ExpanderCodes.exists_split_full_degree_parameter (p n : ℕ) [Fact p.Prime]
    (hPositive : 0 < n) (epsilon : ZMod p)
    (hEpsilon : epsilon ≠ 0) (hNonSquare : ∀ r : ZMod p, r ^ 2 ≠ epsilon) :
    ∃ y r : GaloisField p (2 * n), y ≠ 0 ∧ 1 + y ≠ 0 ∧ r ≠ 0 ∧
      r ^ 2 = algebraMap (ZMod p) (GaloisField p (2 * n)) epsilon ∧
      Irreducible (minpoly (ZMod p) y) ∧
      (minpoly (ZMod p) y).natDegree = 2 * n := by sorry
