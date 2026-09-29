-- Prove2me | Theorems.Thm_WeierstrassProjModel_kw_a2_add_ne_zero_of_pointClass_ne
-- name    : WeierstrassProjModel.kw_a2_add_ne_zero_of_pointClass_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/fbe95063-bd94-541e-83e8-82c41053af58
-- title:
--   Projective addition coordinates do not all vanish for distinct points
-- statement:
--   Let $R$ be a commutative ring, $W$ a Weierstrass curve over $R$, and $F$ a field equipped with an $R$-algebra structure; write $W_F$ for the projective Weierstrass curve `kw_lrApt_WF W F`, namely the projective model of the base change $W \otimes_R F$, whose coefficients are the images of those of $W$ under the structure map. Assume the image of the discriminant $\Delta_W$ under $R \to F$ is nonzero. Let $P, Q : \mathrm{Fin}\,3 \to F$ be two triples of elements of $F$, each satisfying the homogeneous cubic equation of $W_F$ (Mathlib's `Projective.Equation`), each nonzero as a function, and such that their classes $\llbracket P \rrbracket$ and $\llbracket Q \rrbracket$ in `WeierstrassCurve.Projective.PointClass F`, the quotient of $F^3$ by the relation of differing by a unit scalar, are distinct. The conclusion is the disjunction that at least one of the three coordinates of the projective chord addition formulae of $W_F$ evaluated at $(P,Q)$ — `addX`, `addY`, `addZ` — is nonzero; equivalently, the triple $\mathrm{addXYZ}_{W_F}(P,Q)$ is not the zero vector.
--
--   This is the non-degeneracy statement for the chord part of the projective group law: the addition formulae return a genuine point of $\mathbb{P}^2$ whenever the two input points are distinct, the curve being smooth because its discriminant is invertible in $F$. It is used by [`WeierstrassProjModel.kw_a2_exists_sixU_ne_zero_of_pointClass_ne`](thm.html#WeierstrassProjModel.kw_a2_exists_sixU_ne_zero_of_pointClass_ne), where non-vanishing of one of the addition coordinates produces a nonvanishing section on the relevant open of the product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_kw_a2_add_ne_zero_of_pointClass_ne.lean

import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable (F : Type u) [Field F] [Algebra R F]

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem WeierstrassProjModel.kw_a2_add_ne_zero_of_pointClass_ne
    (hΔ : algebraMap R F W.Δ ≠ 0) (P Q : Fin 3 → F)
    (hP : (kw_lrApt_WF W F).Equation P) (hQ : (kw_lrApt_WF W F).Equation Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)
    (hne : (⟦P⟧ : WeierstrassCurve.Projective.PointClass F) ≠ ⟦Q⟧) :
    (kw_lrApt_WF W F).addX P Q ≠ 0 ∨ (kw_lrApt_WF W F).addY P Q ≠ 0
      ∨ (kw_lrApt_WF W F).addZ P Q ≠ 0 := by sorry
