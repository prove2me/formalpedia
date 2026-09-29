-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_grpObj_eq
-- name    : WeierstrassProjModel.RelativeGroupLaw.exists_grpObj_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/6d89e038-505f-546d-9bfb-e34340de7be8
-- title:
--   Relative group law on T-points yields a group object over Spec R
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f \colon A \to \operatorname{Spec} R$ a morphism, and let $G$ be a relative group law on $f$ in the [`WeierstrassProjModel.RelativeGroupLaw`](def/WeierstrassCurve_ProjModel.html#L67) packaging: for every scheme $T$ and every $t \colon T \to \operatorname{Spec} R$ it provides a binary operation `G.mul t`, an element `G.one t` and a unary operation `G.inv t` on the set $\{\varphi \colon T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over $t$, subject to associativity, the two-sided unit laws, the left inverse law, and naturality: for $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$, precomposition with $\psi$ carries `G.mul t` to `G.mul t'`. The assertion is that there is a group-object structure $g$ on the object $f$ of the category of schemes over $\operatorname{Spec} R$ (for the cartesian monoidal structure) inducing $G$ on points: for all $T$, $t$ and all $a, b \colon (T,t) \to (A,f)$ over $\operatorname{Spec} R$, the underlying scheme morphism of `lift a b` followed by `g.mul` is `G.mul t` applied to the underlying morphisms of $a$ and $b$; the underlying morphism of `toUnit (Over.mk t)` followed by `g.one` is `G.one t`; and the underlying morphism of $a$ followed by `g.inv` is `G.inv t` applied to that of $a$.
--
--   This is the representability (Yoneda) direction for relative group laws: a functorial group structure on the $T$-points of $A$ over $\operatorname{Spec} R$ comes from a group-object structure on $A$ in schemes over $\operatorname{Spec} R$. It is the variant of that statement for the `WeierstrassProjModel` packaging of a relative group law, and is used in deducing that the group law of a projective Weierstrass model agrees with the one computed on points over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_exists_grpObj_eq.lean

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.CartesianMonoidalCategory NeronModelInfra
  GoodReductionJacobian WeierstrassProjModel

universe u

theorem WeierstrassProjModel.RelativeGroupLaw.exists_grpObj_eq
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : WeierstrassProjModel.RelativeGroupLaw R f) :
    ∃ g : GrpObj (Over.mk f),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : Over.mk t ⟶ Over.mk f),
        overHomToSchemeHomOver (lift a b ≫ g.mul) =
          G.mul t (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        overHomToSchemeHomOver (toUnit (Over.mk t) ≫ g.one) = G.one t) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : Over.mk t ⟶ Over.mk f),
        overHomToSchemeHomOver (a ≫ g.inv) = G.inv t (overHomToSchemeHomOver a)) := by sorry
