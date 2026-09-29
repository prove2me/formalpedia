-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_cup_mk_left_eq_tateMap
-- name    : Rep.IsTateCupProduct.cup_mk_left_eq_tateMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/4c305460-f111-579c-879d-464910e134b0
-- title:
--   Cup product with a degree-0 Tate class is an induced map
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group. Let $cup$ be a Tate cup-product family, i.e. for all representations $A,B$ of $G$ over $k$ and all integers $p,q,r$ with $p+q=r$ a $k$-bilinear map $\hat H^p(G,A)\times\hat H^q(G,B)\to\hat H^r(G,A\otimes B)$, and assume [`Rep.IsTateCupProduct cup`](def/GroupCohomology_IsTateCupProduct.html#L28): it agrees with any graded cup product on ordinary group cohomology in degrees $(p+1,q+1)$, it is natural with respect to morphisms in both variables via the induced maps [`Rep.tateMap`](def/GroupCohomology_TateShiftMaps.html#L17), and it satisfies the two compatibilities with the Tate connecting maps of short exact sequences (in the first variable without sign, in the second variable up to the sign $(-1)^p$). Let $A,B$ be representations of $G$ over $k$, let $a$ be an element of the submodule $A^G$ of $G$-invariants, and let $\varphi : B \to A\otimes B$ be a morphism of representations with $\varphi(b)=a\otimes_k b$ for all $b\in B$. Then for every integer $q$ and every $y\in\hat H^q(G,B)$, the cup product of the class of $a$ in $\hat H^0(G,A)=A^G/\operatorname{range}(\mathrm{normBar})$ with $y$, formed in total degree $0+q=q$, equals the image of $y$ under the map $\hat H^q(G,B)\to\hat H^q(G,A\otimes B)$ induced by $\varphi$ (group cohomology maps in degrees $\ge 1$, the maps on invariants and on the kernel of the norm in degrees $0$ and $-1$, group homology maps in degrees $\le -2$).
--
--   This is the standard description of the cup product by a class coming from an invariant element: cupping with $[a]\in\hat H^0(G,A)$ is the map induced by $b\mapsto a\otimes b$, in every integer degree. It is used in the development of Tate cohomology to identify cup products concretely, being cited in the proof that cupping with a suitable class is bijective and in the computation $[a]\cup[b]=[a\otimes b]$ in degree $0$; note that equivariance of $b \mapsto a \otimes b$ is assumed rather than asserted, the morphism $\varphi$ being given as a hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_cup_mk_left_eq_tateMap.lean

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

theorem Rep.IsTateCupProduct.cup_mk_left_eq_tateMap {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {cup : Rep.TateCupFamily k G} (hcup : Rep.IsTateCupProduct cup) (A B : Rep.{u} k G)
    (a : A.ρ.invariants) (φ : B ⟶ A ⊗ B) (hφ : ∀ b : B, φ.hom b = (a : A) ⊗ₜ[k] b)
    (q : ℤ) (y : B.tateCohomology q) :
    cup A B 0 q q (zero_add q) (Submodule.Quotient.mk a : A.tateH0) y = (Rep.tateMap φ q).hom y := by sorry
