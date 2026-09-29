-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_exists_cupEv_dual_right_eq
-- name    : Rep.IsTateCupProduct.exists_cupEv_dual_right_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/51f00e84-57b9-5feb-86be-b9b85905e5df
-- title:
--   Right surjectivity of the integral Tate duality pairing
-- statement:
--   Let $G$ be a finite group and let $\mathrm{cup}$ be a family of $\mathbb{Z}$-bilinear maps $\hat H^p(A)\times\hat H^q(B)\to\hat H^r(A\otimes B)$, one for each pair of $\mathbb{Z}$-linear $G$-representations $A,B$ and each triple of integers $p,q,r$ with $p+q=r$, where $\hat H^n$ denotes Tate cohomology as defined by cases: group cohomology $H^{n}$ for $n\ge 1$, the invariants modulo the image of the norm map for $n=0$, the kernel of the norm map on the coinvariants for $n=-1$, and group homology $H_{-n-1}$ for $n\le -2$. Assume $\mathrm{cup}$ satisfies [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28): in strictly positive degrees it agrees with any graded cochain-level cup product, it is natural with respect to pairs of morphisms $\varphi\otimes\psi$ via the induced maps [`Rep.tateMap`](def/GroupCohomology_TateShiftMaps.html#L17), and it is compatible with the connecting maps of short exact sequences in each variable, the left-hand compatibility carrying the sign $(-1)^p$. Let $V$ be a finitely generated free abelian group, $\rho$ a $G$-action on $V$ by $\mathbb{Z}$-linear automorphisms, and write $M=$ `Rep.of ρ`. Let $p,q$ be integers with $p+q=0$ and let $\varphi:\hat H^p(M)\to\hat H^0(\mathbb{Z})$ be $\mathbb{Z}$-linear, $\mathbb{Z}$ carrying the trivial action. Then there is $b\in\hat H^q\bigl(\mathrm{Hom}(M,\mathbb{Z})\bigr)$, the internal hom of the trivial representation $\mathbb{Z}$ by $M$, such that for every $x\in\hat H^p(M)$ the image of $\mathrm{cup}(x,b)$ under the degree-$0$ map induced by the evaluation $M\otimes\mathrm{Hom}(M,\mathbb{Z})\to\mathbb{Z}$ equals $\varphi(x)$.
--
--   This is the surjectivity half of integral Tate duality for a finite group: the pairing $[x,b]=\mathrm{ev}_*(x\cup b)$ realises every homomorphism $\hat H^p(G,M)\to\hat H^0(G,\mathbb{Z})$ in the second variable, complementing the bijectivity statement [`Rep.IsTateCupProduct.bijective_cupEv_dual_left`](thm.html#Rep.IsTateCupProduct.bijective_cupEv_dual_left) in the first variable. It is used to obtain the corresponding surjectivity for the Nakayama pairing in [`Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq`](thm.html#Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_exists_cupEv_dual_right_eq.lean

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

theorem Rep.IsTateCupProduct.exists_cupEv_dual_right_eq {G : Type} [Group G] [Fintype G]
    {cup : Rep.TateCupFamily ℤ G} (hcup : Rep.IsTateCupProduct cup)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)
    (p q : ℤ) (h : p + q = 0) (φ : (Rep.of ρ).tateCohomology p →ₗ[ℤ] (Rep.trivial ℤ G ℤ).tateCohomology 0) :
    ∃ b : ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)).tateCohomology q,
      ∀ x : (Rep.of ρ).tateCohomology p,
        (Rep.tateMap ((ihom.ev (Rep.of ρ)).app (Rep.trivial ℤ G ℤ)) 0).hom
          (cup (Rep.of ρ) ((ihom (Rep.of ρ)).obj (Rep.trivial ℤ G ℤ)) p q 0 h x b) = φ x := by sorry
