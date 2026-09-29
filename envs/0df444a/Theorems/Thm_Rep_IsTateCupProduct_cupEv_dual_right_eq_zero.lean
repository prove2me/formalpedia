-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_cupEv_dual_right_eq_zero
-- name    : Rep.IsTateCupProduct.cupEv_dual_right_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/088e1596-10e1-57b4-ad87-0d8ba6fdd3e2
-- title:
--   Right non-degeneracy of the integral Tate pairing
-- statement:
--   Let $G$ be a finite group and let $cup$ be a family of $\mathbb Z$-bilinear maps $\hat H^p(A)\times\hat H^q(B)\to\hat H^r(A\otimes B)$, one for each pair of $\mathbb Z$-linear $G$-representations $A,B$ and each triple $p+q=r$ of integers, where $\hat H^n$ denotes Tate cohomology, defined as group cohomology in degrees $\ge 1$, as the invariants modulo the image of the norm map in degree $0$, as the kernel of the norm map on the coinvariants in degree $-1$, and as group homology in degrees $\le -2$; assume $cup$ satisfies the predicate [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28), i.e. it agrees with a graded cup product on group cohomology in strictly positive degrees, is natural in both variables with respect to the Tate maps $\mathrm{tateMap}$ induced by morphisms of representations, and commutes with the Tate connecting maps of short exact sequences in the first variable and, up to the sign $(-1)^p$, in the second. Let $V$ be a free abelian group carrying a $\mathbb Z$-linear action $\rho$ of $G$, put $M=\mathrm{Rep.of}\,\rho$ and let $M^\vee=(\mathrm{ihom}\,M).\mathrm{obj}(\mathbb Z)$ be the internal hom into the trivial representation $\mathbb Z$. Let $p+q=0$ and let $b\in\hat H^q(G,M^\vee)$ be such that for every $x\in\hat H^p(G,M)$ the class $\mathrm{ev}_*\big(cup\,x\,b\big)\in\hat H^0(G,\mathbb Z)$ vanishes, where $\mathrm{ev}:M\otimes M^\vee\to\mathbb Z$ is the evaluation morphism and $\mathrm{ev}_*$ is the induced map on $\hat H^0$. Then $b=0$.
--
--   This is the right-hand non-degeneracy half of the integral duality $\hat H^p(G,M)\times\hat H^{-p}(G,\mathrm{Hom}(M,\mathbb Z))\to\hat H^0(G,\mathbb Z)$ for a finite group $G$ acting on a free abelian group; no finiteness of the rank is required for this direction. It is used for the bijectivity of the induced map into the dual, for the corresponding surjectivity statement, and for the non-degeneracy of the Tate–Nakayama pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_cupEv_dual_right_eq_zero.lean

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

theorem Rep.IsTateCupProduct.cupEv_dual_right_eq_zero {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] (ρ : Representation ℤ G V)
    (p q : ℤ) (h : p + q = 0) (b : ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)).tateCohomology q)
    (hb : ∀ x : (Rep.of ρ).tateCohomology p,
      (Rep.tateMap ((ihom.ev (Rep.of ρ)).app (Rep.trivial ℤ G ℤ)) 0).hom
        (cup (Rep.of ρ) ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)) p q 0 h x b) = 0) :
    b = 0 := by sorry
