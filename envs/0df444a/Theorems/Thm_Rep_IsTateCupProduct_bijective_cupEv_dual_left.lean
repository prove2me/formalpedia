-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_bijective_cupEv_dual_left
-- name    : Rep.IsTateCupProduct.bijective_cupEv_dual_left
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/f8b3f088-17c5-5989-91c0-e7308ece8512
-- title:
--   Integral Tate duality via cup product, p+q=0
-- statement:
--   Let $G$ be a finite group and let $\mathrm{cup}$ be a family of $\mathbb{Z}$-bilinear maps $\hat H^p(A)\times\hat H^q(B)\to\hat H^r(A\otimes B)$, one for each pair of $\mathbb{Z}[G]$-representations $A,B$ and each triple $p+q=r$ of integers, where $\hat H^n$ denotes the project's Tate cohomology (group cohomology $H^{n}$ for $n\ge 1$, the invariants modulo the image of the norm map in degree $0$, the kernel of the norm map in degree $-1$, and group homology $H_{-n-1}$ for $n\le -2$). Assume $\mathrm{cup}$ satisfies [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28): in strictly positive degrees it agrees with any graded cup product on ordinary group cohomology, it is natural for morphisms $\varphi\otimes\psi$ of representations via the maps [`Rep.tateMap`](def/GroupCohomology_TateShiftMaps.html#L17), and it commutes with the Tate connecting maps in each variable separately, with the sign $(-1)^p$ in the second variable. Let $V$ be a finitely generated free abelian group with a $\mathbb{Z}$-linear $G$-action $\rho$, put $M=$ `Rep.of ρ` and $M^\vee=(\mathrm{ihom}\,M)(\mathbb{Z})$ the internal Hom into the trivial representation $\mathbb{Z}$, and let $p+q=0$. Then the assignment sending $x\in\hat H^p(M)$ to the linear map $b\mapsto \mathrm{ev}_*(\mathrm{cup}(x,b))$, where $\mathrm{ev}:M\otimes M^\vee\to\mathbb{Z}$ is the evaluation morphism and $\mathrm{ev}_*$ is the induced map on $\hat H^0$, is a bijection $\hat H^p(M)\to \mathrm{Hom}_{\mathbb{Z}}\bigl(\hat H^q(M^\vee),\hat H^0(\mathbb{Z})\bigr)$.
--
--   This is the integral duality theorem for the Tate cohomology of a finite group: for $M$ finitely generated and $\mathbb{Z}$-free the cup-product pairing $\hat H^p(G,M)\times\hat H^{-p}(G,M^\vee)\to\hat H^0(G,\mathbb{Z})\cong\mathbb{Z}/|G|$ is perfect, here in the form that the induced map into the dual of $\hat H^{-p}(G,M^\vee)$ is bijective. It is used to produce duality elements in [`Rep.IsTateCupProduct.exists_cupEv_dual_right_eq`](thm.html#Rep.IsTateCupProduct.exists_cupEv_dual_right_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_bijective_cupEv_dual_left.lean

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

theorem Rep.IsTateCupProduct.bijective_cupEv_dual_left {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)
    (p q : ℤ) (h : p + q = 0) :
    Function.Bijective (fun x : (Rep.of ρ).tateCohomology p =>
      ((Rep.tateMap ((ihom.ev (Rep.of ρ)).app (Rep.trivial ℤ G ℤ)) 0).hom ∘ₗ
        cup (Rep.of ρ) ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)) p q 0 h x :
          ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)).tateCohomology q →ₗ[ℤ]
            (Rep.trivial ℤ G ℤ).tateCohomology 0)) := by sorry
