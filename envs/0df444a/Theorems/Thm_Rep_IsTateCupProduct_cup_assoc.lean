-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_cup_assoc
-- name    : Rep.IsTateCupProduct.cup_assoc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/69c49b2f-737d-538e-97df-3dc893d8dcd6
-- title:
--   Associativity of the Tate cup product in all degrees
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $cup$ be a family which, for all $k$-linear $G$-representations $A,B$ and integers $p,q,r$ with $p+q=r$, gives a $k$-bilinear map $\hat H^p(A)\times\hat H^q(B)\to\hat H^r(A\otimes B)$, where $A.\mathrm{tateCohomology}$ is group cohomology in degrees $\ge 1$, the invariants modulo the image of the norm map in degree $0$, the kernel of the norm map in degree $-1$, and group homology $H_{n+1}$ in degree $-n-2$. Assume `hcup : Rep.IsTateCupProduct cup`, i.e. $cup$ agrees in degrees $(p+1,q+1)$ with any graded cup product on group cohomology, is natural in both variables with respect to [`Rep.tateMap`](def/GroupCohomology_TateShiftMaps.html#L17) of a tensor product $\varphi\otimes\psi$ of morphisms, and satisfies the two connecting-map identities $\delta(x\cup y)=(\delta x)\cup y$ and $\delta(x\cup y)=(-1)^p\,x\cup(\delta y)$ for short exact sequences remaining exact after tensoring on the relevant side. Let $A,B,C$ be representations, let $p,q,r,r_{12},r_{23},r_{123}$ be integers with $p+q=r_{12}$, $q+r=r_{23}$ and $r_{12}+r=r_{123}$, and let $x\in\hat H^p(A)$, $y\in\hat H^q(B)$, $z\in\hat H^r(C)$. Then $(x\cup y)\cup z$, formed in degrees $(r_{12},r)\to r_{123}$, equals the image of $x\cup(y\cup z)$, formed in degrees $(p,r_{23})\to r_{123}$, under [`Rep.tateMap`](def/GroupCohomology_TateShiftMaps.html#L17) applied to the inverse associator $(\alpha_{A,B,C})^{-1}\colon A\otimes(B\otimes C)\to (A\otimes B)\otimes C$ in degree $r_{123}$.
--
--   This is the associativity of the cup product on Tate cohomology of a finite group, stated with the three intermediate degrees as separate variables constrained by additivity hypotheses, so that no transport along $(p+q)+r=p+(q+r)$ occurs. It is used in the construction and vanishing statements for the Tate–Nakayama pairing, namely [`Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq`](thm.html#Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq) and [`Rep.IsTateCupProduct.tateNakayamaPairing_right_eq_zero`](thm.html#Rep.IsTateCupProduct.tateNakayamaPairing_right_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_cup_assoc.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep MonoidalCategory

theorem Rep.IsTateCupProduct.cup_assoc {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B C : Rep.{u} k G)
    (p q r r₁₂ r₂₃ r₁₂₃ : ℤ) (h₁₂ : p + q = r₁₂) (h₂₃ : q + r = r₂₃) (h : r₁₂ + r = r₁₂₃)
    (x : A.tateCohomology p) (y : B.tateCohomology q) (z : C.tateCohomology r) :
    cup (A ⊗ B) C r₁₂ r r₁₂₃ h (cup A B p q r₁₂ h₁₂ x y) z
      = (Rep.tateMap (α_ A B C).inv r₁₂₃).hom (cup A (B ⊗ C) p r₂₃ r₁₂₃ (by omega) x (cup B C q r r₂₃ h₂₃ y z)) := by sorry
