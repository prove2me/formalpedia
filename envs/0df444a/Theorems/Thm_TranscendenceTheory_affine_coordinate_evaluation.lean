-- Prove2me | Theorems.Thm_TranscendenceTheory_affine_coordinate_evaluation
-- name    : TranscendenceTheory.affine_coordinate_evaluation
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T20:28:12.454432+00:00
-- url     : https://prove2.me/theorems/97b777a3-60dc-430c-bd7d-92dddbcb3e7e
-- title:
--   Exact evaluation in an affine polynomial coordinate
-- statement:
--   Let R and S be commutative semirings, with S an R-algebra, and let σ be any type of polynomial variables with decidable equality. Fix i∈σ, a polynomial p∈R[σ], and values v:σ→S. Suppose the degree of p in the variable i is at most one.
--
--   Write v₀ for v with its i-th coordinate replaced by zero. Then
--
--   $$p(v)=p(v_0)+v(i)\,(\partial_i p)(v_0).$$
--
--   Thus the constant and linear parts are explicitly recovered by setting the selected coordinate to zero in p and in its formal partial derivative. The other coordinates are arbitrary. No characteristic-zero, field, integral-domain, or nonvanishing assumption is required.
-- source:
--   Derived affine-coordinate evaluation step for https://prove2.me/theorems/c5fda26c-bd8b-41f7-8c44-455600d1082e. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is a derived algebraic tool for the interpolation frontier. The geometric zero estimate remains open. Primary Lean sources: Mathlib Algebra/MvPolynomial/Basic.lean, Degrees.lean, Eval.lean and PDeriv.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. Expanding a polynomial into supported monomials proves exact first-order Taylor evaluation in a variable of degree at most one. Applying this to the reduced wp-prime coordinate writes each formal evaluation as A plus wp-prime times B, with A and B evaluated at wp-prime zero. Both directions preserve every witness, interpolation weight and numerical bound.

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv

open MvPolynomial

theorem TranscendenceTheory.affine_coordinate_evaluation
    (R S σ : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
    [DecidableEq σ] (i : σ) (p : MvPolynomial σ R) (v : σ → S)
    (hp : p.degreeOf i ≤ 1) :
    MvPolynomial.aeval v p =
      MvPolynomial.aeval (Function.update v i 0) p +
        v i * MvPolynomial.aeval (Function.update v i 0) (MvPolynomial.pderiv i p) := by sorry
