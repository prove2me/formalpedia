-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_cupEv_characterDual_zero_eq_zero
-- name    : Rep.IsTateCupProduct.cupEv_characterDual_zero_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/d4f51c11-38d0-51b7-b332-2addd2058c83
-- title:
--   Right non-degeneracy of the Tate pairing in degrees (-1,0)
-- statement:
--   Let $G$ be a finite group and let $cup$ be a family assigning, to representations $A,B$ over $\mathbb Z$ and integers $p,q,r$ with $p+q=r$, a $\mathbb Z$-bilinear map $\hat H^p(G,A)\times\hat H^q(G,B)\to\hat H^r(G,A\otimes B)$ on Tate cohomology (here $\hat H^{n}$ is group cohomology for $n\ge 1$, group homology for $n\le -2$, the invariants modulo the image of the norm map for $n=0$, and the kernel of the norm map on coinvariants for $n=-1$), and assume $cup$ satisfies the axioms of [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28): agreement with a graded cup product on group cohomology in degrees $\ge 1$, functoriality in both arguments under $\varphi\otimes\psi$, and compatibility with the connecting maps of a short exact sequence tensored on the right, respectively on the left up to the sign $(-1)^p$. Let $M$ be a representation of $G$ over $\mathbb Z$, let $M^{*}=(\mathrm{ihom}\,M).\mathrm{obj}$ applied to the trivial representation $\mathbb Q/\mathbb Z$ (written `AddCircle (1 : ℚ)`) be the internal hom object, and let $a\in\hat H^{0}(G,M^{*})$. If for every $x\in\hat H^{-1}(G,M)$ the image of $cup\,M\,M^{*}\,(-1)\,0\,(-1)\,x\,a$ under the map induced in degree $-1$ by the evaluation morphism $M\otimes M^{*}\to\mathbb Q/\mathbb Z$ vanishes, then $a=0$.
--
--   This is one half of the non-degeneracy of the Tate duality pairing $\hat H^{-1}(G,M)\times\hat H^{0}(G,M^{*})\to\hat H^{-1}(G,\mathbb Q/\mathbb Z)$ for a finite group $G$ and the character module $M^{*}=\operatorname{Hom}(M,\mathbb Q/\mathbb Z)$, namely that an element of $\hat H^{0}(G,M^{*})$ pairing to zero with everything is itself zero. It is used by [`Rep.IsTateCupProduct.cupEv_characterDual_eq_zero`](thm.html#Rep.IsTateCupProduct.cupEv_characterDual_eq_zero) in the development of duality for Tate cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_cupEv_characterDual_zero_eq_zero.lean

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

theorem Rep.IsTateCupProduct.cupEv_characterDual_zero_eq_zero {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup) (M : Rep ℤ G)
    (a : ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).tateCohomology 0)
    (ha : ∀ x : M.tateCohomology (-1),
      (Rep.tateMap ((ihom.ev M).app (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1)).hom
        (cup M ((ihom M).obj (Rep.trivial ℤ G (AddCircle (1 : ℚ)))) (-1) 0 (-1) (add_zero (-1)) x a) = 0) :
    a = 0 := by sorry
