-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_bijective_cup_of_h1_h2
-- name    : Rep.IsTateCupProduct.bijective_cup_of_h1_h2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/55907933-0f1d-5f4f-a329-a49039f8c704
-- title:
--   Tate's theorem in cup-product form with free coefficients
-- statement:
--   Let $G$ be a finite group, $C$ a $G$-module over $\mathbb{Z}$ (an object of `Rep ℤ G`) and $u \in H^2(G, C)$. Assume that for every subgroup $S \le G$: $H^1(S, C) = 0$ (the object `groupCohomology (Rep.res S.subtype C) 1` is a zero object); $H^2(S, C)$ has cardinality $\#S$; and the $\mathbb{Z}$-span of the single element $u_S :=$ image of $u$ under `groupCohomology.map S.subtype (𝟙 _) 2` is all of $H^2(S,C)$. Let $V$ be a free $\mathbb{Z}$-module carrying a representation $\rho$ of $G$, let $S \le G$ be a subgroup, and let $\mathrm{cup}$ be a family of $\mathbb{Z}$-bilinear maps $\hat H^p(S,A) \times \hat H^q(S,B) \to \hat H^r(S, A \otimes B)$, for all $A,B$ in `Rep ℤ S` and all integers $p+q=r$, satisfying [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28): it agrees with any graded cup product on group cohomology in degrees $\ge 1$, is natural in both variables along `tateMap`, and commutes with the Tate connecting maps of short exact sequences in each variable, with sign $(-1)^p$ in the left variable. Here $\hat H^n$ denotes the Tate groups: group cohomology for $n \ge 1$, invariants modulo the norm for $n = 0$, the kernel of the norm for $n = -1$, and group homology for $n \le -2$. Then for every integer $q$ the map $x \mapsto u_S \cup x$ is a bijection from $\hat H^q(S, V)$ onto $\hat H^{q+2}(S, C \otimes V)$, the target being the Tate group in degree $q+2$ of the restriction to $S$ of $C \otimes \rho$ (restriction commuting with the tensor product).
--
--   This is Tate's theorem: cup product with a fundamental class $u_S$ of $H^2(S,C)$ shifts Tate cohomology by $2$, here in map form and with coefficients twisted by an arbitrary $\mathbb{Z}$-free representation $V$. It feeds the construction and vanishing statements for the Tate–Nakayama pairing, [`Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq`](thm.html#Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq) and [`Rep.IsTateCupProduct.tateNakayamaPairing_right_eq_zero`](thm.html#Rep.IsTateCupProduct.tateNakayamaPairing_right_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_bijective_cup_of_h1_h2.lean

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

theorem Rep.IsTateCupProduct.bijective_cup_of_h1_h2 {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] (ρ : Representation ℤ G V)
    (S : Subgroup G) [Fintype S] (cup : Rep.TateCupFamily ℤ S) (hcup : Rep.IsTateCupProduct cup) (q : ℤ) :
    Function.Bijective (fun x : (Rep.res S.subtype (Rep.of ρ)).tateCohomology q =>
      (cup (Rep.res S.subtype C) (Rep.res S.subtype (Rep.of ρ)) 2 q (q + 2) (add_comm 2 q)
        ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u) x :
          (Rep.res S.subtype (C ⊗ Rep.of ρ)).tateCohomology (q + 2))) := by sorry
