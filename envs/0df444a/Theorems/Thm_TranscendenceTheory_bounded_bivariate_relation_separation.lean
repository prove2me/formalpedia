-- Prove2me | Theorems.Thm_TranscendenceTheory_bounded_bivariate_relation_separation
-- name    : TranscendenceTheory.bounded_bivariate_relation_separation
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-14T16:43:22.621387+00:00
-- url     : https://prove2.me/theorems/03fdcdd1-4ff9-4f8f-a9e3-08b1661dcd40
-- title:
--   Bounded polynomial separation and linear interpolation
-- statement:
--   Let K be a field, and let A and L be commutative K-algebras. Fix x,y in A, u,v in L, and natural numbers b,s. There is a bivariate polynomial P whose outer degree is at most s and whose coefficient degrees are at most b, with P(x,y)=0 but P(u,v) nonzero, if and only if there is no K-linear map T:A→L satisfying T(x^j y^i)=u^j v^i for all 0≤i≤s and 0≤j≤b.
--
--   The algebras need not be finite dimensional, reduced, or nontrivial. The bounds b=0 and s=0 are included. The map T is only required to be linear; it is not assumed to be multiplicative.
-- source:
--   Derived linear separation step for https://prove2.me/theorems/220d1ce8-77e0-4688-b5f4-240f40909f00. Mission context: Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2, Theorem A.3 and Proposition A.1; https://doi.org/10.1017/S001309152610145X. This is a derived algebraic tool, not a completion of the paper zero estimate. Primary Lean sources: Mathlib Algebra/Polynomial/AlgebraMap.lean, LinearAlgebra/Basis/VectorSpace.lean and LinearAlgebra/Isomorphisms.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. Bounded polynomial separation is equivalent to failure to interpolate the corresponding bounded monomials by a linear map. The first isomorphism theorem and extension of linear maps prove the difficult implication, preserving every degree bound.

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms

noncomputable section
open Polynomial
open scoped Classical

theorem TranscendenceTheory.bounded_bivariate_relation_separation
    (K A L : Type*) [Field K] [CommRing A] [Algebra K A]
    [CommRing L] [Algebra K L] (x y : A) (u v : L) (b s : ℕ) :
    (∃ P : Polynomial (Polynomial K),
      P.natDegree ≤ s ∧ (∀ i, (P.coeff i).natDegree ≤ b) ∧
        P.eval₂ (Polynomial.aeval x).toRingHom y = 0 ∧
        P.eval₂ (Polynomial.aeval u).toRingHom v ≠ 0) ↔
      ¬ ∃ T : A →ₗ[K] L,
        ∀ i ≤ s, ∀ j ≤ b, T (x ^ j * y ^ i) = u ^ j * v ^ i := by sorry
