-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_skeletalClassification
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.skeletalClassification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:45:31.766495+00:00
-- url     : https://prove2.me/theorems/0b557cf2-d2d9-4b86-990b-3f914d4181d5
-- title:
--   Classification of skeletal Gr-categories
-- statement:
--   Let $\mathcal C$ and $\mathcal D$ be skeletal Gr-categories. Let $G_{\mathcal C}$ and $G_{\mathcal D}$ denote their actual object groups under tensor product, and put $A_{\mathcal C}=\operatorname{Aut}(I_{\mathcal C})$ and $A_{\mathcal D}=\operatorname{Aut}(I_{\mathcal D})$. Let $\rho_{\mathcal C},\rho_{\mathcal D}$ be the conjugation actions, and $a_{\mathcal C},a_{\mathcal D}$ their associator cocycles, using left coordinates and all unit and inverse transports.
--
--   Then $\mathcal C$ and $\mathcal D$ are strongly monoidally equivalent if and only if there are group isomorphisms $\phi:G_{\mathcal C}\to G_{\mathcal D}$ and $\psi:A_{\mathcal C}\to A_{\mathcal D}$ and an arbitrary cochain $f:G_{\mathcal C}^2\to A_{\mathcal D}$ such that, for every $g,h,k$ and $b\in A_{\mathcal C}$,
--
--   $$
--   \rho_{\mathcal D}(\phi(g))\psi(b)=\psi(\rho_{\mathcal C}(g)b),\qquad
--   a_{\mathcal D}(\phi(g),\phi(h),\phi(k))-\psi(a_{\mathcal C}(g,h,k))=(d_\phi f)(g,h,k),
--   $$
--
--   where $(d_\phi f)(g,h,k)=\rho_{\mathcal D}(\phi(g))f(h,k)-f(gh,k)+f(g,hk)-f(g,h)$. The coefficient groups are written additively here; Lean uses their existing multiplicative automorphism-group law. A tensor- and unit-preserving bijection represents the object-group isomorphism.
--
--   This identifies exactly when the transported associator classes agree, while retaining unmarked equivalences and arbitrary source unitors.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 19, Appendix A, Theorem 15: classification of skeletal Gr-categories (original seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

/-- Theorem 15, PDF pp. 19–20: classification of actual skeletal
Gr-categories. A bijection preserving tensor and unit is precisely an
isomorphism of their object groups; psi is an actual unit-group isomorphism.
The invariant relation is stated using its computed cocycle representatives,
which is exactly equality of their transported H3 classes.
Printed f:Gprime²→A is changed to f:G²→Aprime because the difference
is Aprime-valued on G. The associator uses the left-coordinate correction
of PDF p. 8, rather than asserting the printed equation for right coordinates. -/
theorem skeletalClassification
    {C : Type u} {D : Type u1} [Category.{v} C] [Category.{v1} D]
    [MonoidalCategory C] [MonoidalCategory D]
    (hC : IsWeakTwoGroup C) (hD : IsWeakTwoGroup D)
    (sC : Skeletal C) (sD : Skeletal D) :
    Nonempty (GrEquivalence C D) ↔
      ∃ phi : C ≃ D,
        (∀ x y : C, phi (x ⊗ y) = phi x ⊗ phi y) ∧
        phi (𝟙_ C) = 𝟙_ D ∧
        ∃ psi : Aut (𝟙_ C) ≃* Aut (𝟙_ D),
          (∀ x : C, ∀ a : Aut (𝟙_ C),
            actionCoordinate hD (phi x) (psi a) = psi (actionCoordinate hC x a)) ∧
          ∃ f : C → C → Aut (𝟙_ D), ∀ x y z : C,
            associatorCoordinate hD sD (phi x) (phi y) (phi z) *
              (psi (associatorCoordinate hC sC x y z))⁻¹ =
                pulledCoboundary hD phi f x y z := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P06
