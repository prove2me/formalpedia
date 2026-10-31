-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_restrainedInvariants
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.restrainedInvariants
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:53:13.680992+00:00
-- url     : https://prove2.me/theorems/77b1ad2b-68c3-48e7-b510-a940c05cd796
-- title:
--   All three invariant consequences of restraint
-- statement:
--   Let $\mathcal C$ be a restrained Pic-category. Let $G=\pi_0(\mathcal C)$ have multiplication induced by tensor product. Compute the unit-automorphism action $\rho$ and associator cochain $a$ from the canonical skeleton with its transported monoidal structure. Then all three assertions hold:
--
--   $$
--   gh=hg\quad(g,h\in G),\qquad
--   \rho(x)(b)=b\quad(x\in\operatorname{Sk}(\mathcal C),\ b\in\operatorname{Aut}(I)),\qquad
--   \exists f:\operatorname{Sk}(\mathcal C)^2\to\operatorname{Aut}(I),\quad a=df.
--   $$
--
--   Here $df(x,y,z)=\rho(x)f(y,z)-f(xy,z)+f(x,yz)-f(x,y)$, so the last assertion is exactly $[a]=0$. These are conclusions derived from restraint, with no trivial-action or zero-class input hypothesis. Together they explain why only two abelian groups are needed in the restrained classification.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 13, §5: all three consequences of restraint

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

/-- Section 5, PDF p. 13: all three consequences of restraint.
The object-class group is abelian, the action on the actual transported
skeleton is trivial, and its actual associator is a coboundary, exactly
expressing zero Sinh class. None of these conclusions is an input. -/
theorem restrainedInvariants {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [SymmetricCategory C]
    (h : IsWeakTwoGroup C) (r : Restrained C) :
    letI := classGroup h
    (∀ a b : ObjectClasses C, a * b = b * a) ∧
    ∃ hs : IsWeakTwoGroup (Skeleton C),
      (∀ x : Skeleton C, ∀ a : Aut (𝟙_ (Skeleton C)),
        actionCoordinate hs x a = a) ∧
      ∃ f : Skeleton C → Skeleton C → Aut (𝟙_ (Skeleton C)),
        ∀ x y z : Skeleton C,
          associatorCoordinate hs (skeleton_skeletal C) x y z =
            pulledCoboundary hs id f x y z := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P06
