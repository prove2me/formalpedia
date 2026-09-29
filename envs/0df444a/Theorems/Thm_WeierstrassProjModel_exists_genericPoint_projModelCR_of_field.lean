-- Prove2me | Theorems.Thm_WeierstrassProjModel_exists_genericPoint_projModelCR_of_field
-- name    : WeierstrassProjModel.exists_genericPoint_projModelCR_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/827ca2a1-ae52-5067-9294-86fb60418314
-- title:
--   Generic point of the projective Weierstrass model over a field
-- statement:
--   Let $K$ be a field and let $V$ be a projective Weierstrass curve over $K$, that is, a tuple of coefficients $a_1,a_2,a_3,a_4,a_6 \in K$ with associated homogeneous cubic `V.polynomial` in the three variables indexed by `Fin 3`; no hypothesis of nonsingularity or of nonvanishing discriminant is imposed. Grade `MvPolynomial (Fin 3) K` by total degree and let $\mathcal{A} =$ `projModelGradingCR V` be the induced $\mathbb{N}$-grading on the quotient ring `ProjModelRingCR V` $=$ `MvPolynomial (Fin 3) K` $/\,(V.polynomial)$, whose degree-$i$ piece is the $K$-submodule image of the degree-$i$ homogeneous submodule under the quotient map; the ideal divided out is the span of `V.polynomial`, packaged as a homogeneous ideal. The assertion is that there exists a point $\eta$ of `Proj` $\mathcal{A}$ — i.e. a homogeneous ideal of the quotient that is prime and does not contain the irrelevant ideal — such that $\eta$'s homogeneous ideal is the zero ideal $\bot$, and such that the closure of the singleton $\{\eta\}$ in the topological space `Proj` $\mathcal{A}$ is the whole space. Thus the projective Weierstrass model over a field is irreducible with generic point given by the zero ideal.
--
--   This is the existence of a generic point on the projective Weierstrass model of a curve given by a Weierstrass cubic over a field, a form of irreducibility of that model. It is used in the proof that multiplication by $n$ on the scheme attached to a Weierstrass model is locally quasi-finite.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_exists_genericPoint_projModelCR_of_field.lean

import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry WeierstrassProjModel

universe u

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem WeierstrassProjModel.exists_genericPoint_projModelCR_of_field
    {K : Type u} [Field K] (V : WeierstrassCurve.Projective K) :
    ∃ η : Proj (projModelGradingCR V),
      η.asHomogeneousIdeal = ⊥ ∧
      closure ({η} : Set (Proj (projModelGradingCR V))) = Set.univ := by sorry
