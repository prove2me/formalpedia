-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_exists_ratFunc_eq_sum_simpleFractions_of_squarefree
-- name    : QEC.Coding.AlgebraicGeometry.Differential.exists_ratFunc_eq_sum_simpleFractions_of_squarefree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:43:58.734577+00:00
-- url     : https://prove2.me/theorems/9aa083e2-b166-4439-9894-42b77bc6fbc3
-- title:
--   Differential: exists rat Func eq sum simple Fractions of squarefree
-- statement:
--   A proper rational function with squarefree normalized denominator is a
--   finite sum of proper simple fractions with monic irreducible denominators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SquarefreePartialFraction.lean#L36-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Rational/SquarefreePartialFraction.lean#L36-L167

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.PartialFractions
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimplePoleDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SquarefreePartialFraction
set_option autoImplicit false
open scoped BigOperators Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open UniqueFactorizationMonoid
variable {k : Type*} [Field k]

theorem QEC.Coding.AlgebraicGeometry.Differential.exists_ratFunc_eq_sum_simpleFractions_of_squarefree
    (f : RatFunc k)
    (hdegree : f.num.degree < f.denom.degree)
    (hsquarefree : Squarefree f.denom) :
    ∃ (s : Finset k[X]) (r : k[X] → k[X]),
      (∀ q ∈ s, q.Monic ∧ Irreducible q ∧ (r q).degree < q.degree) ∧
        f = ∑ q ∈ s,
          algebraMap k[X] (RatFunc k) (r q) /
            algebraMap k[X] (RatFunc k) q := by sorry
