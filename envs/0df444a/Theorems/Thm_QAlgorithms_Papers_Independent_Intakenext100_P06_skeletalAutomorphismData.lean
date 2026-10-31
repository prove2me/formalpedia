-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_skeletalAutomorphismData
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.skeletalAutomorphismData
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:50:22.515983+00:00
-- url     : https://prove2.me/theorems/0ce65b9e-5550-4180-88ac-b4b95d68a1c4
-- title:
--   Automorphism groups, conjugation action, and tensor reconstruction
-- statement:
--   Let $\mathcal C$ be a skeletal Gr-category, $G$ its actual object group, and $A=\operatorname{Aut}(I)$. Every arrow has equal source and target; the group $A$ is abelian; and tensoring unit automorphisms agrees with composition after transport by a unitor. For every $g$, the map $R_g:\operatorname{Aut}(g)\to A$ given by $R_g(f)=1_{g^{-1}}\otimes f$, with the necessary inverse and unit transports, is a group isomorphism. There is an automorphic group action $\rho:G\to\operatorname{Aut}(A)$ given by
--
--   $$
--   \rho(g)(a)=1_g\otimes a\otimes1_{g^{-1}}.
--   $$
--
--   Writing $L_g(f)=f\otimes1_{g^{-1}}$ with the corresponding endpoint transports, tensoring arbitrary automorphisms is reconstructed by
--
--   $$
--   L_{g\otimes h}(f\otimes k)=L_g(f)\,\rho(g)(L_h(k)).
--   $$
--
--   All displayed coordinates use specified weak-inverse identifications, and the action additionally uses the right unitor. This retains every clause of the source's automorphism description, including the construction of the action.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 7, §3: unit automorphisms, all object automorphisms and the action

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

section AutomorphismCoordinates

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Section 3, PDF pp. 7–8: all automorphism data, including the
constructed group action, the source's right-coordinate identifications,
Eckmann–Hilton and the tensor reconstruction law in left coordinates. -/
theorem skeletalAutomorphismData (h : IsWeakTwoGroup C) (hs : Skeletal C) :
    (∀ (x y : C) (f : x ⟶ y), x = y) ∧
    (∀ a b : Aut (𝟙_ C), a * b = b * a) ∧
    (∀ a b : (𝟙_ C ⟶ 𝟙_ C),
      (λ_ (𝟙_ C)).inv ≫ (a ⊗ₘ b) ≫ (λ_ (𝟙_ C)).hom = a ≫ b) ∧
    (∀ x : C, ∃ e : Aut x ≃* Aut (𝟙_ C),
      ∀ f, e f = rightCoordinate h x f) ∧
    ∃ k : Group C,
      letI := k
      (∀ x y : C, x * y = x ⊗ y) ∧ (1 : C) = 𝟙_ C ∧
      ∃ rho : C →* MulAut (Aut (𝟙_ C)),
        (∀ x a, rho x a = actionCoordinate h x a) ∧
        (∀ x y : C, ∀ f : Aut x, ∀ g : Aut y,
          leftCoordinate h (x ⊗ y) (f ⊗ᵢ g) =
            leftCoordinate h x f * rho x (leftCoordinate h y g)) := by sorry

end AutomorphismCoordinates

end QAlgorithms.Papers.Independent.Intakenext100.P06
