-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_injective_cupEv_negOne_characterDual
-- name    : Rep.IsTateCupProduct.injective_cupEv_negOne_characterDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/73441ab5-1298-5f7d-94dc-6e977e669380
-- title:
--   Left non-degeneracy of the Tate pairing in degrees (-1,0)
-- statement:
--   Let $G$ be a finite group and let $\mathrm{cup}$ be a family of $\mathbb{Z}$-bilinear maps $\hat H^{p}(G,A)\times\hat H^{q}(G,B)\to\hat H^{r}(G,A\otimes B)$, one for each pair of $\mathbb{Z}$-linear representations $A,B$ of $G$ and each triple of integers $p+q=r$, where $\hat H^{n}$ denotes the project's Tate cohomology: group cohomology in degrees $\ge 1$, $A^{G}/\operatorname{im}\bar N$ in degree $0$, $\ker\bar N\subseteq A_{G}$ in degree $-1$, and group homology in degrees $\le -2$. Assume $\mathrm{cup}$ satisfies [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28), i.e. it agrees with any graded cup product on group cohomology in bidegrees $(p+1,q+1)$, it is compatible with maps $\varphi\otimes\psi$ induced by pairs of morphisms of representations, and it interchanges with the Tate connecting maps of a short exact sequence tensored on the right, respectively on the left (the latter up to the sign $(-1)^{p}$). Let $M$ be a $\mathbb{Z}$-linear representation of $G$ and put $Q=\mathbb{Q}/\mathbb{Z}$ with trivial $G$-action, realised as $\mathbb{R}/\mathbb{Z}$-valued rationals. Then the map sending $x\in\hat H^{-1}(G,M)$ to the linear map $a\mapsto \mathrm{ev}_{*}(x\cup a)$ from $\hat H^{0}\bigl(G,\underline{\mathrm{Hom}}(M,Q)\bigr)$ to $\hat H^{-1}(G,Q)$, where $\mathrm{ev}$ is the evaluation morphism $M\otimes\underline{\mathrm{Hom}}(M,Q)\to Q$ and $\mathrm{ev}_{*}$ the induced map in degree $-1$, is injective.
--
--   This is the left-hand non-degeneracy half of Tate duality for a finite group in the bidegree $(-1,0)$, with $\mathbb{Q}/\mathbb{Z}$ as dualising module: a class in $\hat H^{-1}(G,M)$ killed by pairing with every class in $\hat H^{0}(G,\underline{\mathrm{Hom}}(M,\mathbb{Q}/\mathbb{Z}))$ vanishes. It feeds [`Rep.IsTateCupProduct.injective_cupEv_characterDual`](thm.html#Rep.IsTateCupProduct.injective_cupEv_characterDual), where the corresponding injectivity is transported to other degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_injective_cupEv_negOne_characterDual.lean

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

theorem Rep.IsTateCupProduct.injective_cupEv_negOne_characterDual {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup) (M : Rep ℤ G) :
    Function.Injective (fun x : M.tateCohomology (-1) =>
      ((Rep.tateMap ((ihom.ev M).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom ∘ₗ
        cup M ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1) 0 (-1) (add_zero (-1)) x :
          ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).tateCohomology 0 →ₗ[ℤ]
            (Rep.trivial ℤ G (AddCircle (1 : ℚ))).tateCohomology (-1))) := by sorry
