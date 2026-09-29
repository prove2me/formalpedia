-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_nsmul_comp_eq_of_mul_comp_eq
-- name    : WeierstrassProjModel.RelativeGroupLaw.nsmul_comp_eq_of_mul_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/971ecd5d-ff42-58ed-82e3-0fdccb6df523
-- title:
--   Transport of n-fold multiples along a group-law morphism
-- statement:
--   Let $g : R \to R'$ be a homomorphism of commutative rings, let $f : A \to \operatorname{Spec} R$ and $f' : A' \to \operatorname{Spec} R'$ be morphisms of schemes, and let $\pi : A' \to A$ be a morphism making the square with $\pi$, $f'$, $f$ and $\operatorname{Spec}(g)$ a pullback square (hypothesis `hP`). Let $G$ be a relative group law on $f$ over $R$ and $G'$ one on $f'$ over $R'$: that is, for each scheme $T$ and each $t : T \to \operatorname{Spec} R$ (resp. over $\operatorname{Spec} R'$) a multiplication, unit and inversion on the set of sections $\{\varphi : T \to A \mid \varphi \circ f = t\}$ satisfying associativity, the unit laws, left inverses, and compatibility with precomposition in $T$. Assume $\pi$ intertwines the two multiplications and the two units: for every scheme $S$, every $s : S \to \operatorname{Spec} R'$ and all sections $x, y$ of $f'$ over $s$, the underlying morphism of $G'.\mathrm{mul}\,s\,x\,y$ followed by $\pi$ equals that of $G.\mathrm{mul}$ at the base point $\operatorname{Spec}(g) \circ s$ applied to $\pi \circ x$ and $\pi \circ y$ (these are sections of $f$ over $\operatorname{Spec}(g) \circ s$ because the square commutes), and likewise $G'.\mathrm{one}\,s$ followed by $\pi$ is $G.\mathrm{one}$ at $\operatorname{Spec}(g) \circ s$. The conclusion is the corresponding identity for all $n$-fold multiples: for every $s : S \to \operatorname{Spec} R'$, every $n \in \mathbb{N}$ and every section $x$ of $f'$ over $s$, the underlying morphism of $G'.\mathrm{nsmul}\,s\,n\,x$ followed by $\pi$ equals that of $G.\mathrm{nsmul}$ at $\operatorname{Spec}(g) \circ s$ applied to $\pi \circ x$, where $\mathrm{nsmul}$ is defined by recursion, $\mathrm{nsmul}\,0\,x = \mathrm{one}$ and $\mathrm{nsmul}\,(n+1)\,x = \mathrm{mul}\,(\mathrm{nsmul}\,n\,x)\,x$.
--
--   This is the statement that a morphism of schemes compatible with two relative group laws and with their units also transports multiplication-by-$n$, in the base-change situation where $A'$ is the pullback of $A$ along $\operatorname{Spec}(g)$. It is used in the study of the multiplication-by-$n$ maps on a projective Weierstrass model and their expansion in the chart at the origin, via [`WeierstrassCurve.DrinfeldGlobal.exists_originChart_comp_schemeNsmul_eq_of_formalChart`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_originChart_comp_schemeNsmul_eq_of_formalChart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_nsmul_comp_eq_of_mul_comp_eq.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.RelativeGroupLaw.nsmul_comp_eq_of_mul_comp_eq
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R')
    {A A' : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) (f' : A' ⟶ Spec (CommRingCat.of R'))
    (π : A' ⟶ A) (hP : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (G : RelativeGroupLaw R f) (G' : RelativeGroupLaw R' f')
    (hmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R')) (x y : SchemeHomOver s f'),
      (G'.mul s x y).1 ≫ π =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom g))
          ⟨x.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, y.2]⟩).1)
    (hone : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R')),
      (G'.one s).1 ≫ π = (G.one (s ≫ Spec.map (CommRingCat.ofHom g))).1)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R')) (n : ℕ) (x : SchemeHomOver s f') :
    (G'.nsmul s n x).1 ≫ π =
      (G.nsmul (s ≫ Spec.map (CommRingCat.ofHom g)) n
        ⟨x.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩).1 := by sorry
