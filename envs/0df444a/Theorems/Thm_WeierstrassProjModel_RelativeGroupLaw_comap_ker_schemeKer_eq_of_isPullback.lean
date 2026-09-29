-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_comap_ker_schemeKer_eq_of_isPullback
-- name    : WeierstrassProjModel.RelativeGroupLaw.comap_ker_schemeKer_eq_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/400b6d3f-ecc4-5c64-971a-30e787a0ce0f
-- title:
--   q-torsion ideal sheaf transports along a cartesian square
-- statement:
--   Let $f : B \to T$ be a homomorphism of commutative rings, let $p : E \to \operatorname{Spec} B$ and $p' : E' \to \operatorname{Spec} T$ be separated morphisms of schemes, and let $\pi : E' \to E$ be such that the square with $\pi$, $p'$, $p$ and $\operatorname{Spec}(f)$ is cartesian (in particular $\pi$ followed by $p$ equals $p'$ followed by $\operatorname{Spec}(f)$). Let $G$ be a `RelativeGroupLaw` for $p$ and $L$ one for $p'$, i.e. functorial group structures (multiplication, unit, inverse, associativity, unit and inverse laws, and naturality in the base) on the sets $\{\varphi : S \to E \mid \varphi \text{ over } s\}$ of sections over each $s : S \to \operatorname{Spec} B$, resp. over each $s : S \to \operatorname{Spec} T$. Assume $\pi$ is compatible with the two laws: for every scheme $S$, every $s : S \to \operatorname{Spec} T$ and all sections $x, y$ of $p'$ over $s$, the product $L.\mathrm{mul}\,s\,x\,y$ followed by $\pi$ equals the $G$-product, over $s$ followed by $\operatorname{Spec}(f)$, of $x\pi$ and $y\pi$; and the unit of $L$ at $\mathrm{id}_{\operatorname{Spec} T}$ followed by $\pi$ equals $\operatorname{Spec}(f)$ followed by the unit of $G$ at $\mathrm{id}_{\operatorname{Spec} B}$. Fix $q \in \mathbb{N}$. Write $[q]_G = G.\mathrm{schemeNsmul}\,q : E \to E$ for the $q$-fold sum of the tautological point, and likewise $[q]_L$. The conclusion is an equality of ideal sheaf data on $E' \times_{\operatorname{Spec} T} \operatorname{Spec} T$ (the pullback of $p'$ along $\mathrm{id}$): the kernel ideal sheaf of the first projection of the pullback of $[q]_G$ against the unit section $\operatorname{Spec} B \to E$, pulled back first along $E \times_{\operatorname{Spec} B} \operatorname{Spec} T \to E$ and then along the morphism induced by $\pi$ on the first factor and the identity on the second, coincides with the kernel ideal sheaf of the first projection of the pullback of $[q]_L$ against the unit section $\operatorname{Spec} T \to E'$, followed by the canonical morphism $E' \to E' \times_{\operatorname{Spec} T} \operatorname{Spec} T$.
--
--   This records that the $q$-torsion closed subscheme of a relative group law is compatible with base change: the torsion ideal sheaf of $E/B$, transported to $E'$ across a cartesian square whose horizontal map respects multiplication and unit, is the torsion ideal sheaf of $E'/T$. It is stated for an abstract square, and is used in the Drinfeld level-structure material on projective Weierstrass models, where it is applied both to a genuine coefficient base change and to a change of Weierstrass coordinates; it is cited by [`WeierstrassCurve.DrinfeldGlobal.isLevel_act_of_comp_projMap_eq`](thm.html#WeierstrassCurve.DrinfeldGlobal.isLevel_act_of_comp_projMap_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_comap_ker_schemeKer_eq_of_isPullback.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra

theorem WeierstrassProjModel.RelativeGroupLaw.comap_ker_schemeKer_eq_of_isPullback
    {B T : Type u} [CommRing B] [CommRing T] (f : B →+* T)
    {E E' : Scheme.{u}} (p : E ⟶ Spec (CommRingCat.of B)) (p' : E' ⟶ Spec (CommRingCat.of T))
    [IsSeparated p] [IsSeparated p'] (π : E' ⟶ E)
    (hP : IsPullback π p' p (Spec.map (CommRingCat.ofHom f)))
    (G : RelativeGroupLaw B p) (L : RelativeGroupLaw T p')
    (hmul : ∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver s p'),
      (L.mul s x y).1 ≫ π =
        (G.mul (s ≫ Spec.map (CommRingCat.ofHom f))
          ⟨x.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ π, by rw [Category.assoc, hP.w, ← Category.assoc, y.2]⟩).1)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ π =
      Spec.map (CommRingCat.ofHom f) ≫ (G.one (𝟙 (Spec (CommRingCat.of B)))).1)
    (q : ℕ) :
    Scheme.IdealSheafData.comap
      (Scheme.IdealSheafData.comap (Scheme.Hom.ker (pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1))
        (pullback.fst p (Spec.map (CommRingCat.ofHom f))))
      (pullback.lift (pullback.fst p' (𝟙 _) ≫ π) (pullback.snd p' (𝟙 _))
        (by rw [Category.assoc, hP.w, ← Category.assoc, pullback.condition, Category.assoc, Category.id_comp])) =
      Scheme.Hom.ker (pullback.fst (L.schemeNsmul q) (L.one (𝟙 _)).1 ≫
        pullback.lift (𝟙 E') p' (by rw [Category.id_comp, Category.comp_id])) := by sorry
