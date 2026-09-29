-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_iso_comp_eq_and_comp_hom_eq_mul
-- name    : WeierstrassProjModel.RelativeGroupLaw.exists_iso_comp_eq_and_comp_hom_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/000a5817-3057-54be-9418-56bbff8fb6ec
-- title:
--   Translation by a section is an automorphism over the base
-- statement:
--   Let $R$ be a commutative ring and let $f : A \to \operatorname{Spec} R$ be a morphism of schemes equipped with a `RelativeGroupLaw` $G$: for each test scheme $T$ and each $t : T \to \operatorname{Spec} R$, operations `mul`, `one`, `inv` on the set of morphisms $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$, satisfying associativity, two-sided unit laws and left inverse, together with naturality of `mul` under precomposition with any $\psi : T' \to T$ over the base. Let $P$ be a section of $f$, i.e. a morphism $P : \operatorname{Spec} R \to A$ with $P$ followed by $f$ the identity. The assertion is that there exists an isomorphism $\tau : A \xrightarrow{\sim} A$ such that $\tau$ followed by $f$ equals $f$, and such that for every scheme $X$, every $t : X \to \operatorname{Spec} R$ and every $x : X \to A$ over $t$, the composite $x$ followed by $\tau$ equals $G.\mathrm{mul}_t(x, t \circ P)$, where $t \circ P$ is the point obtained from $P$ by precomposition with $t$. Only existence is claimed, and only the forward direction of $\tau$ is asserted to lie over the base.
--
--   This is the standard fact that right translation by a section of a scheme carrying a relative group law is an automorphism over the base, represented on relative points by multiplication by that section. It is used in the Drinfeld-type argument bounding torsion ideals by basis divisors, where cosets of a section must be moved to the origin.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_exists_iso_comp_eq_and_comp_hom_eq_mul.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.RelativeGroupLaw.exists_iso_comp_eq_and_comp_hom_eq_mul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    ∃ τ : A ≅ A,
      τ.hom ≫ f = f ∧
      ∀ {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        x.1 ≫ τ.hom = (G.mul t x (schemeHomOverComp t (Category.comp_id t) P)).1 := by sorry
