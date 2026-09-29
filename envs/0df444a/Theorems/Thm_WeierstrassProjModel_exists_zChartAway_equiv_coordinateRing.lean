-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
-- name    : WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/9c497cad-c0a5-5c03-a6e8-fddf7319677e
-- title:
--   The Z-chart of the projective Weierstrass model is the affine coordinate ring
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$, with homogeneous cubic $V.\mathrm{polynomial} \in R[X_0,X_1,X_2]$ and associated affine polynomial $V.\mathrm{toAffine.polynomial} \in R[X][Y]$ (here $R[X][Y]$ is `Polynomial (Polynomial R)`). Grade the quotient $B = R[X_0,X_1,X_2]/(V.\mathrm{polynomial})$ by letting the degree-$n$ piece be the image under the quotient map of the $R$-submodule of homogeneous polynomials of degree $n$, and form the degree-zero homogeneous localisation of $B$ away from the class of $X_2$. The assertion is that there exists a ring homomorphism $f$ from this homogeneous localisation to $R[X][Y]/(V.\mathrm{toAffine.polynomial})$ such that: $f$ is bijective; the composite of the canonical map $R \to B_0$ followed by the inclusion of $B_0$ into the localisation and then $f$ equals the structure map $R \to R[X][Y]/(V.\mathrm{toAffine.polynomial})$; and for every $n \in \mathbb{N}$ and every $b \in R[X_0,X_1,X_2]$ homogeneous of degree $n \cdot 1$, the element $\bar b/\bar X_2^{\,n}$ is sent by $f$ to the class of $b(X, Y, 1)$, i.e. of the image of $b$ under the $R$-algebra map $X_0 \mapsto X$, $X_1 \mapsto Y$, $X_2 \mapsto 1$. No smoothness or discriminant hypothesis is imposed.
--
--   This is the chart dictionary identifying the standard affine chart $D_+(X_2)$ of the $\operatorname{Proj}$ of the projective Weierstrass model with the spectrum of the affine Weierstrass coordinate ring, together with compatibility over the base and an explicit formula on generators. It is used downstream for base change of the $Z$-chart, for smoothness and relative dimension statements about the model, and for identifying its points; the ambient identification of $R[X_0,X_1,X_2]_{(X_2)}$ with $R[X][Y]$ is supplied by [`WeierstrassProjModel.exists_ringEquiv_zChartAwayDegreeZero_univ`](thm.html#WeierstrassProjModel.exists_ringEquiv_zChartAwayDegreeZero_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) :
    ∃ f : HomogeneousLocalization.Away (WeierstrassProjModel.projModelGradingCR V)
          (Ideal.Quotient.mk (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
            (MvPolynomial.X 2 : MvPolynomial (Fin 3) R)) →+*
        (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}),
      Function.Bijective f ∧
      f.comp ((HomogeneousLocalization.fromZeroRingHom (WeierstrassProjModel.projModelGradingCR V)
            (Submonoid.powers (Ideal.Quotient.mk
              (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
              (MvPolynomial.X 2 : MvPolynomial (Fin 3) R)))).comp
          (algebraMap R (WeierstrassProjModel.projModelGradingCR V 0)))
        = algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}) ∧
      ∀ (n : ℕ) (b : MvPolynomial (Fin 3) R)
        (hb : b ∈ MvPolynomial.homogeneousSubmodule (Fin 3) R (n • 1)),
        f (HomogeneousLocalization.Away.mk (WeierstrassProjModel.projModelGradingCR V)
            (HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _
              ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 2)))
            n
            (Ideal.Quotient.mk (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal b)
            (HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _ hb))
          = Ideal.Quotient.mk _
              (MvPolynomial.aeval
                (![Polynomial.C Polynomial.X, Polynomial.X, 1] : Fin 3 → Polynomial (Polynomial R)) b) := by sorry
