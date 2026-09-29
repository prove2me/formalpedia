-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_injective_cupEv_characterDual
-- name    : Rep.IsTateCupProduct.injective_cupEv_characterDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/609adaa3-ba75-55f4-bfe9-1a098ce8b325
-- title:
--   Injectivity of Tate duality pairing in all degrees
-- statement:
--   Let $G$ be a finite group and let $\cup$ be a Tate cup-product family over $\mathbb{Z}$ for $G$: an assignment to each pair of representations $A,B$ of $G$ over $\mathbb{Z}$ and each triple of integers $p,q,r$ with $p+q=r$ of a $\mathbb{Z}$-bilinear map $\hat H^p(A)\times\hat H^q(B)\to\hat H^r(A\otimes B)$ on Tate cohomology (the complete cohomology whose value in degree $n+1\ge 1$ is $H^{n+1}(G,A)$, in degree $0$ is the invariants modulo the image of the norm, in degree $-1$ is the kernel of the norm on $A$, and in degree $-(n+1)\le -1$ is $H_{n+1}(G,A)$). Assume the hypothesis [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28) for this family, i.e. that it agrees with a graded cup product on ordinary cohomology in degrees $\ge 1$ in each variable, is natural with respect to $\varphi\otimes\psi$ for morphisms $\varphi,\psi$ of representations, and satisfies the two connecting-map identities $\delta(x\cup y)=\delta x\cup y$ for short exact sequences tensored on the right and $\delta(x\cup y)=(-1)^p\,x\cup\delta y$ for short exact sequences tensored on the left. Let $M$ be a representation of $G$ over $\mathbb{Z}$, write $M^{*}=(\mathrm{ihom}\,M)(\mathbb{Q}/\mathbb{Z})$ for the internal hom into the trivial representation $\mathbb{Q}/\mathbb{Z}$ (realised as `AddCircle (1 : ℚ)`), and let $p,q$ be integers with $p+q=-1$. Then the map
--   $$\hat H^p(M)\longrightarrow \operatorname{Hom}_{\mathbb{Z}}\bigl(\hat H^q(M^{*}),\,\hat H^{-1}(\mathbb{Q}/\mathbb{Z})\bigr),\qquad x\longmapsto \bigl(y\mapsto \mathrm{ev}_{*}(x\cup y)\bigr),$$
--   is injective, where $\mathrm{ev}$ is the evaluation morphism $M\otimes M^{*}\to\mathbb{Q}/\mathbb{Z}$ and $\mathrm{ev}_{*}$ is the induced map on Tate cohomology in degree $-1$.
--
--   This is the left non-degeneracy half of Tate duality for a finite group with $\mathbb{Q}/\mathbb{Z}$ coefficients, asserting injectivity (but not surjectivity) of $x\mapsto\langle x,-\rangle$ in every pair of complementary degrees. It is used to obtain the bijectivity statement [`Rep.IsTateCupProduct.bijective_cupEv_dual_left`](thm.html#Rep.IsTateCupProduct.bijective_cupEv_dual_left) and the surjectivity-type statement [`Rep.IsTateCupProduct.exists_cupEv_dual_right_eq`](thm.html#Rep.IsTateCupProduct.exists_cupEv_dual_right_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_injective_cupEv_characterDual.lean

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
open CategoryTheory Rep MonoidalCategory

theorem Rep.IsTateCupProduct.injective_cupEv_characterDual {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup) (M : Rep ℤ G) (p q : ℤ) (h : p + q = -1) :
    Function.Injective (fun x : M.tateCohomology p =>
      ((Rep.tateMap ((ihom.ev M).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom ∘ₗ
        cup M ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) p q (-1) h x :
          ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).tateCohomology q →ₗ[ℤ]
            (Rep.trivial ℤ G (AddCircle (1 : ℚ))).tateCohomology (-1))) := by sorry
