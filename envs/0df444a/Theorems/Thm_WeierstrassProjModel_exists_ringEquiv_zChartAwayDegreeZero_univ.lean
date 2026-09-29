-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_ringEquiv_zChartAwayDegreeZero_univ
-- name    : WeierstrassProjModel.exists_ringEquiv_zChartAwayDegreeZero_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/a1eb969c-f414-50b8-8875-1d94e3af2552
-- title:
--   Z-chart dehomogenisation: degree-zero part away from X₂
-- statement:
--   Let $R$ be a commutative ring in an arbitrary universe, and grade the polynomial ring $R[X_0,X_1,X_2] =$ `MvPolynomial (Fin 3) R` by total degree, the homogeneous component of degree $n$ being `homogeneousSubmodule (Fin 3) R n`. The theorem asserts a conjunction. First, there exists a ring isomorphism $e$ from the degree-zero part of the homogeneous localisation away from the homogeneous element $X_2$, namely `HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R) (X 2)`, onto the iterated polynomial ring `Polynomial (Polynomial R)`, such that for every natural number $n$ and every $a \in R[X_0,X_1,X_2]$ homogeneous of degree $n \cdot 1 = n$, the value of $e$ on the class of $a/X_2^{\,n}$ equals the image of $a$ under the $R$-algebra map sending $X_0 \mapsto$ `Polynomial.C Polynomial.X` (the inner variable $x$), $X_1 \mapsto$ `Polynomial.X` (the outer variable $y$) and $X_2 \mapsto 1$. Second, for every projective Weierstrass curve $V$ over $R$, the same substitution carries the homogeneous Weierstrass cubic `V.polynomial` to the affine Weierstrass polynomial `V.toAffine.polynomial` in $R[x][y]$.
--
--   This is the standard identification of the affine chart $D_+(X_2)$ of $\mathbb{P}^2_R$ with $\operatorname{Spec} R[x][y]$ via dehomogenisation $a \mapsto a(x,y,1)$, together with the compatibility of this identification with the passage from the homogeneous Weierstrass cubic to the affine Weierstrass polynomial. It is used to identify the $Z$-chart ring of a projective Weierstrass model with a quotient of $R[x][y]$, as in [`WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing`](thm.html#WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing) and in the base-change square [`WeierstrassProjModel.kw_bc_awayIsPushout_Z_univ`](thm.html#WeierstrassProjModel.kw_bc_awayIsPushout_Z_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_ringEquiv_zChartAwayDegreeZero_univ.lean

import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem WeierstrassProjModel.exists_ringEquiv_zChartAwayDegreeZero_univ (R : Type u) [CommRing R] :
    (∃ e : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 3) R)
          (X 2 : MvPolynomial (Fin 3) R) ≃+*
        Polynomial (Polynomial R),
      ∀ (n : ℕ) (a : MvPolynomial (Fin 3) R)
        (ha : a ∈ homogeneousSubmodule (Fin 3) R (n • 1)),
        e (HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin 3) R)
            ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ 2)) n a ha)
          = aeval (![Polynomial.C Polynomial.X, Polynomial.X, 1] :
              Fin 3 → Polynomial (Polynomial R)) a) ∧
    ∀ (V : WeierstrassCurve.Projective R),
      aeval (![Polynomial.C Polynomial.X, Polynomial.X, 1] :
          Fin 3 → Polynomial (Polynomial R)) V.polynomial
        = V.toAffine.polynomial := by sorry
