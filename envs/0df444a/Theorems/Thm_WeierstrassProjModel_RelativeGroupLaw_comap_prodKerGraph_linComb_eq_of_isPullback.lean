-- Prove2me | Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_comap_prodKerGraph_linComb_eq_of_isPullback
-- name    : WeierstrassProjModel.RelativeGroupLaw.comap_prodKerGraph_linComb_eq_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/18cb038e-374f-5eed-8152-cd6e9e7fefa7
-- title:
--   Graph-ideal product of [a]P+[b]Q transports along a cartesian square
-- statement:
--   Let $f : B \to T$ be a homomorphism of commutative rings, let $p : E \to \operatorname{Spec} B$ and $p' : E' \to \operatorname{Spec} T$ be separated morphisms of schemes, and let $\pi : E' \to E$ be such that the square formed by $\pi$, $p'$, $p$ and $\operatorname{Spec}(f)$ is cartesian. Let $G$ be a relative group law for $p$ and $L$ one for $p'$: that is, for every scheme $S$ and every structure morphism $s$ to the base, a multiplication, unit and inverse on the sections of $p$ (resp. $p'$) over $s$ — pairs consisting of a morphism to $E$ (resp. $E'$) whose composite with $p$ (resp. $p'$) is $s$ — satisfying associativity, the unit and inverse laws, and naturality in $s$. Assume $\pi$ is compatible with the two laws: composing an $L$-product of two sections over $s$ with $\pi$ gives the $G$-product of the two composites, viewed over $s$ followed by $\operatorname{Spec}(f)$; and composing the $L$-unit over the identity of $\operatorname{Spec} T$ with $\pi$ gives $\operatorname{Spec}(f)$ followed by the $G$-unit over the identity of $\operatorname{Spec} B$. Let $q$ be a natural number and let $P, Q$ be sections of $p'$ over the identity of $\operatorname{Spec} T$, together with proofs that $P$ and $Q$ composed with $\pi$ and then with $p$ both equal $\operatorname{Spec}(f)$. Consider, for $i \in \mathrm{Fin}(q\cdot q)$, the section $[\,i/q\,](\pi \circ P) + [\,i \bmod q\,](\pi \circ Q)$ of $p$ over $\operatorname{Spec}(f)$, where the multiples are the iterated $G$-multiplications starting from the $G$-unit, and correspondingly $[\,i/q\,]P + [\,i \bmod q\,]Q$ for $L$ over the identity. Then the pullback along the morphism from $\operatorname{pullback}(p', \mathbf 1)$ to $\operatorname{pullback}(p, \operatorname{Spec}(f))$ induced by $\pi$ on the first factor and the identity on the second, of the product over $i$ of the kernel ideal sheaves of the graphs of the $G$-sections, equals the product over $i$ of the kernel ideal sheaves of the graphs of the corresponding $L$-sections.
--
--   This is the base-change compatibility of the relative effective divisor $\sum_{a,b<q}\Gamma([a]P+[b]Q)$ attached to two sections of a relative group scheme, in the form needed to compare division structures on a Weierstrass model and on its base change. It is used in the Drinfeld-level part of the development, where level structures on the projective Weierstrass model are shown to be preserved under the cartesian square of such models induced by a coefficient homomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassProjModel_RelativeGroupLaw_comap_prodKerGraph_linComb_eq_of_isPullback.lean

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

theorem WeierstrassProjModel.RelativeGroupLaw.comap_prodKerGraph_linComb_eq_of_isPullback
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
    (q : ℕ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) p')
    (hPp : (P.1 ≫ π) ≫ p = Spec.map (CommRingCat.ofHom f))
    (hQp : (Q.1 ≫ π) ≫ p = Spec.map (CommRingCat.ofHom f)) :
    Scheme.IdealSheafData.comap
      (prodKerGraph p
        (fun i : Fin (q * q) ↦ (G.mul (Spec.map (CommRingCat.ofHom f))
          (G.nsmul _ (i.val / q) ⟨P.1 ≫ π, hPp⟩) (G.nsmul _ (i.val % q) ⟨Q.1 ≫ π, hQp⟩)).1)
        (fun i ↦ (G.mul (Spec.map (CommRingCat.ofHom f))
          (G.nsmul _ (i.val / q) ⟨P.1 ≫ π, hPp⟩) (G.nsmul _ (i.val % q) ⟨Q.1 ≫ π, hQp⟩)).2))
      (pullback.lift (pullback.fst p' (𝟙 _) ≫ π) (pullback.snd p' (𝟙 _))
        (by rw [Category.assoc, hP.w, ← Category.assoc, pullback.condition, Category.assoc, Category.id_comp])) =
      prodKerGraph p'
        (fun i : Fin (q * q) ↦ (L.mul (𝟙 _) (L.nsmul _ (i.val / q) P) (L.nsmul _ (i.val % q) Q)).1)
        (fun i ↦ (L.mul (𝟙 _) (L.nsmul _ (i.val / q) P) (L.nsmul _ (i.val % q) Q)).2) := by sorry
