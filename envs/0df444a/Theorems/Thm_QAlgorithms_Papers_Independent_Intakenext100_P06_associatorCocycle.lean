-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_associatorCocycle
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.associatorCocycle
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:51:01.889541+00:00
-- url     : https://prove2.me/theorems/53282a96-2a05-4f7c-872c-8ebc24408a0f
-- title:
--   The associator satisfies the 3-cocycle equation
-- statement:
--   Let $\mathcal C$ be a skeletal Gr-category. Let $A=\operatorname{Aut}(I)$, let $\rho$ be the conjugation action, and obtain $a(g,h,k)\in A$ by transporting the associator to an automorphism of $(g\otimes h)\otimes k$ and then taking its left coordinate $\alpha\otimes1_{(ghk)^{-1}}$. In additive notation for the abelian group $A$, for every $w,x,y,z$,
--
--   $$
--   \rho(w)a(x,y,z)-a(wx,y,z)+a(w,xy,z)-a(w,x,yz)+a(w,x,y)=0.
--   $$
--
--   Lean writes this equality multiplicatively, replacing each minus by an inverse. The printed right-coordinate extraction is changed to the displayed left coordinate to agree with the source's left-action differential; all endpoint transports are explicit. This is the cocycle underlying the Sính invariant.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 8, §3, equation (6): associator 3-cocycle

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

section AutomorphismCoordinates

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Section 3, equation (6), PDF pp. 8–9: the associator is a 3-cocycle.
Uses the corrected left coordinates described above and binders w,x,y,z,
in place of the printed g1,...,g4 followed by g0,...,g3.
Aut(I) is written multiplicatively, so inverse signs are the printed minuses. -/
theorem associatorCocycle (h : IsWeakTwoGroup C) (hs : Skeletal C) :
    ∀ w x y z : C,
      actionCoordinate h w (associatorCoordinate h hs x y z) *
        (associatorCoordinate h hs (w ⊗ x) y z)⁻¹ *
        associatorCoordinate h hs w (x ⊗ y) z *
        (associatorCoordinate h hs w x (y ⊗ z))⁻¹ *
        associatorCoordinate h hs w x y = 1 := by sorry

end AutomorphismCoordinates

end QAlgorithms.Papers.Independent.Intakenext100.P06
