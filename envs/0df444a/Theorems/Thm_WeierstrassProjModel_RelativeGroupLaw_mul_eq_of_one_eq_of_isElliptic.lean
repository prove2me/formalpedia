-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic
-- name    : WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/517147ae-4db0-5f2b-bdbd-337d961a93e7
-- title:
--   Relative group laws with equal unit section coincide
-- statement:
--   Let $R$ be a commutative ring and let $V$ be a projective Weierstrass curve over $R$ whose associated affine Weierstrass curve is elliptic (its discriminant is a unit). Write $p =$ `projModelStrCR V` for the structure morphism $\mathrm{Proj}$ of the graded quotient of the homogeneous coordinate ring of $V$ to $\operatorname{Spec} R$, obtained from `Proj.toSpecZero` followed by the morphism induced by $R \to$ (degree-zero part). Let $G_0, G_1$ be two relative group laws on $p$: each consists of operations `mul`, `one`, `inv` on the sets $\{\varphi : T \to \mathrm{Proj} \mid \varphi \circ p = t\}$ of $T$-points over $t : T \to \operatorname{Spec} R$, for all schemes $T$, satisfying associativity, both unit laws, a left inverse law, and compatibility of `mul` with composition $\psi$ with $\psi \circ t = t'$. Assume the underlying morphisms $\operatorname{Spec} R \to \mathrm{Proj}$ of the two unit sections over $t = \mathrm{id}_{\operatorname{Spec} R}$ are equal. Then for every scheme $T$, every $t : T \to \operatorname{Spec} R$ and all $T$-points $x, y$ over $t$, one has $G_0.\mathrm{mul}\,t\,x\,y = G_1.\mathrm{mul}\,t\,x\,y$.
--
--   This is the rigidity statement that a group law on the projective model of an elliptic curve over an arbitrary base is determined by its unit section, so that the group structure on a Weierstrass model need not be specified beyond its identity. It is used downstream to compare group laws arising from different constructions, e.g. in the transport and relabelling of level structures and in the compatibility of group laws with morphisms of projective models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_mul_eq_of_one_eq_of_isElliptic.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.RelativeGroupLaw.mul_eq_of_one_eq_of_isElliptic
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) [V.toAffine.IsElliptic]
    (G₀ G₁ : RelativeGroupLaw R (projModelStrCR V))
    (h1 : (G₀.one (𝟙 (Spec (CommRingCat.of R)))).1 = (G₁.one (𝟙 (Spec (CommRingCat.of R)))).1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t (projModelStrCR V)) :
    G₀.mul t x y = G₁.mul t x y := by sorry
