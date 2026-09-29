-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_yChartAway_equiv_coordinateRing
-- name    : WeierstrassProjModel.exists_yChartAway_equiv_coordinateRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/d17a3a5a-405f-5a92-b162-4f3431cc64e8
-- title:
--   The Y-chart of the projective Weierstrass model
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$, with homogeneous cubic $F =$ `V.polynomial` in $R[X_0,X_1,X_2]$. Grade $\mathcal B = R[X_0,X_1,X_2]/(F)$ by the family `projModelGradingCR`, whose $i$-th term is the image under the quotient map of the $R$-submodule of forms of degree $i$, the ideal $(F)$ being homogeneous. The assertion is the existence of a ring homomorphism $f$ from the degree-zero homogeneous localisation of this graded quotient at the class of $X_1$ to the ring $R[Y_0,Y_1]/\mathfrak a$, where $\mathfrak a$ is the span of the range of the one-element family whose value is the dehomogenisation $F(Y_0,1,Y_1)$, obtained by the substitution $X_0\mapsto Y_0$, $X_1\mapsto 1$, $X_2\mapsto Y_1$, such that: $f$ is bijective; $f$ composed with the structure map $R \to \mathcal B_0 \to \mathcal B_{(X_1)}$ (the degree-zero inclusion into the homogeneous localisation at the powers of the class of $X_1$) equals the algebra map of $R$ into $R[Y_0,Y_1]/\mathfrak a$; and for every $n \in \mathbb N$ and every $b \in R[X_0,X_1,X_2]$ homogeneous of degree $n$, $f$ sends the fraction with numerator the class of $b$ and denominator the $n$-th power of the class of $X_1$ to the class of $b(Y_0,1,Y_1)$.
--
--   This identifies the affine coordinate ring of the chart $D_+(X_1)$ of the projective Weierstrass model — the chart containing the point at infinity $[0:1:0]$ — with the quotient of a polynomial ring in two variables by the cubic dehomogenised at $X_1 = 1$, compatibly with the structure map over $R$ and explicitly on fractions of homogeneous elements. The single generator of the ideal is presented as the range of a family indexed by a one-element type, the shape in which standard-smooth presentations of such quotients are given. It is used in the analysis of the two-chart cover $D_+(X_1) \cup D_+(X_2)$ of the model, in particular in the finiteness and surjectivity statements for Frobenius-type morphisms on the charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_yChartAway_equiv_coordinateRing.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem WeierstrassProjModel.exists_yChartAway_equiv_coordinateRing
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) :
    ∃ f : HomogeneousLocalization.Away (WeierstrassProjModel.projModelGradingCR V)
          (Ideal.Quotient.mk (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
            (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)) →+*
        (MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range fun _ : Fin 1 =>
          MvPolynomial.aeval
            (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) R) V.polynomial)),
      Function.Bijective f ∧
      f.comp ((HomogeneousLocalization.fromZeroRingHom (WeierstrassProjModel.projModelGradingCR V)
            (Submonoid.powers (Ideal.Quotient.mk
              (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
              (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)))).comp
          (algebraMap R (WeierstrassProjModel.projModelGradingCR V 0)))
        = algebraMap R (MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range fun _ : Fin 1 =>
            MvPolynomial.aeval
              (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) R)
              V.polynomial)) ∧
      ∀ (n : ℕ) (b : MvPolynomial (Fin 3) R)
        (hb : b ∈ MvPolynomial.homogeneousSubmodule (Fin 3) R (n • 1)),
        f (HomogeneousLocalization.Away.mk (WeierstrassProjModel.projModelGradingCR V)
            (HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _
              ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 1)))
            n
            (Ideal.Quotient.mk (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal b)
            (HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _ hb))
          = Ideal.Quotient.mk _
              (MvPolynomial.aeval
                (![MvPolynomial.X 0, 1, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) R) b) := by sorry
