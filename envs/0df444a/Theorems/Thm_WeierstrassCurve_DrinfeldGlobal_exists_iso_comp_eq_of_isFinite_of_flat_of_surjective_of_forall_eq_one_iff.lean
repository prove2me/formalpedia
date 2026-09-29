-- Prove2me | Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_iso_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one_iff
-- name    : WeierstrassCurve.DrinfeldGlobal.exists_iso_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/04ead7ad-201c-5613-aad2-a352177ea62e
-- title:
--   Isomorphism between quotients with a common kernel
-- statement:
--   Let $A$ be a commutative ring and let $\mathcal{G}$ be a family of group laws over $A$, that is, an assignment to every $A$-algebra $T$ and every projective Weierstrass curve $W$ over $T$ with invertible discriminant of a relative group law on the structure morphism `projModelStrCR W` over $\operatorname{Spec} T$ (functorial multiplication, unit and inverse on $S$-points with the group axioms and compatibility under base change). Assume $\mathcal{G}$ is chord–tangent, i.e. for each such $T$, $W$ and $\Delta$-unit there is an `ev` with `IsPointsEval W (𝒢 T W hΔ) ev`, and that $\mathcal{G}$ has origin identity, i.e. there is a ring homomorphism $\chi$ from `OriginChartRing W` to $T$ which is an origin chart section for the unit point $\mathcal{G}(\mathbb{1})$ and sends `xOverY W` and `zOverY W` to $0$. Let $T$ be an $A$-algebra, let $W_1,W_2,W_3$ be Weierstrass curves over $T$ with $\Delta_i$ a unit, and let $f$ and $g$ be morphisms from the Proj model of $W_1$ to those of $W_2$, resp. $W_3$, commuting with the structure morphisms to $\operatorname{Spec} T$. Assume $f$ and $g$ are homomorphisms on points: for every scheme $S$, every $t : S \to \operatorname{Spec} T$ and all $S$-points $x,y$ of the model of $W_1$ over $t$, composing the $\mathcal{G}$-product of $x$ and $y$ with $f$ (resp. $g$) equals the $\mathcal{G}$-product of $x\circ f$ and $y\circ f$ (resp. of $x \circ g$, $y \circ g$). Assume further that $f$ and $g$ are finite, flat, locally of finite presentation and surjective, and that they have the same kernel on points: for all $t$ and all $S$-points $x$ of $W_1$ over $t$, the point $x$ followed by $f$ is the unit point of $\mathcal{G}(W_2)$ if and only if $x$ followed by $g$ is the unit point of $\mathcal{G}(W_3)$. Then there is an isomorphism $\Psi$ between the Proj models of $W_2$ and $W_3$ such that $\Psi$ lies over $\operatorname{Spec} T$ (its forward direction followed by `projModelStrCR W₃` is `projModelStrCR W₂`), $f$ followed by $\Psi$ equals $g$, and $\Psi$ carries the distinguished section `kwZeroSect` of the model of $W_2$ to that of $W_3$.
--
--   This is the statement that two finite flat surjective homomorphisms out of the same elliptic curve with the same kernel on points identify their targets: the induced map of quotients is an isomorphism over the base preserving the zero sections. It is used in the construction of an isomorphism of Proj models from a Frobenius/Verschiebung datum, [`WeierstrassCurve.DrinfeldGlobal.exists_iso_projModelCR_map_map_of_frobenius_of_comp_schemeNsmul_eq_one_of_nsmul_eq_one`](thm.html#WeierstrassCurve.DrinfeldGlobal.exists_iso_projModelCR_map_map_of_frobenius_of_comp_schemeNsmul_eq_one_of_nsmul_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_DrinfeldGlobal_exists_iso_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one_iff.lean

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.exists_iso_comp_eq_of_isFinite_of_flat_of_surjective_of_forall_eq_one_iff
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (T : Type) [CommRing T] [Algebra A T]
    (W₁ W₂ W₃ : WeierstrassCurve T) (hΔ₁ : IsUnit W₁.Δ) (hΔ₂ : IsUnit W₂.Δ) (hΔ₃ : IsUnit W₃.Δ)
    (f : projModelCR W₁.toProjective ⟶ projModelCR W₂.toProjective)
    (hf : f ≫ projModelStrCR W₂.toProjective = projModelStrCR W₁.toProjective)
    (g : projModelCR W₁.toProjective ⟶ projModelCR W₃.toProjective)
    (hg : g ≫ projModelStrCR W₃.toProjective = projModelStrCR W₁.toProjective)
    (hfhom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t (projModelStrCR W₁.toProjective)),
      (⟨((𝒢 T W₁ hΔ₁).mul t x y).1 ≫ f, by rw [Category.assoc, hf]; exact ((𝒢 T W₁ hΔ₁).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR W₂.toProjective)) =
        (𝒢 T W₂ hΔ₂).mul t ⟨x.1 ≫ f, by rw [Category.assoc, hf]; exact x.2⟩ ⟨y.1 ≫ f, by rw [Category.assoc, hf]; exact y.2⟩)
    (hghom : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t (projModelStrCR W₁.toProjective)),
      (⟨((𝒢 T W₁ hΔ₁).mul t x y).1 ≫ g, by rw [Category.assoc, hg]; exact ((𝒢 T W₁ hΔ₁).mul t x y).2⟩ : SchemeHomOver t (projModelStrCR W₃.toProjective)) =
        (𝒢 T W₃ hΔ₃).mul t ⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ ⟨y.1 ≫ g, by rw [Category.assoc, hg]; exact y.2⟩)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    [IsFinite g] [Flat g] [LocallyOfFinitePresentation g] [Surjective g]
    (hker : ∀ {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x : SchemeHomOver t (projModelStrCR W₁.toProjective)),
      (⟨x.1 ≫ f, by rw [Category.assoc, hf]; exact x.2⟩ : SchemeHomOver t (projModelStrCR W₂.toProjective)) = (𝒢 T W₂ hΔ₂).one t ↔
      (⟨x.1 ≫ g, by rw [Category.assoc, hg]; exact x.2⟩ : SchemeHomOver t (projModelStrCR W₃.toProjective)) = (𝒢 T W₃ hΔ₃).one t) :
    ∃ Ψ : projModelCR W₂.toProjective ≅ projModelCR W₃.toProjective,
      Ψ.hom ≫ projModelStrCR W₃.toProjective = projModelStrCR W₂.toProjective ∧
      f ≫ Ψ.hom = g ∧
      (kwZeroSect T W₂).1 ≫ Ψ.hom = (kwZeroSect T W₃).1 := by sorry
