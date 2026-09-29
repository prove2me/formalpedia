-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_tateNakayamaPairing_right_eq_zero_of_shortExact
-- name    : Rep.IsTateCupProduct.tateNakayamaPairing_right_eq_zero_of_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/3a44f7a1-6c14-570b-8265-5031b66aba6d
-- title:
--   Right non-degeneracy of Tate–Nakayama pairing after δ
-- statement:
--   Let $G$ be a finite group and $C$ a representation of $G$ over $\mathbb{Z}$, and let $u \in H^2(G,C)$ be a class such that, for every subgroup $S \le G$: $H^1(S, C|_S) = 0$; the cardinality of $H^2(S, C|_S)$ equals $|S|$ (for $S$ finite); and the restriction of $u$ to $H^2(S, C|_S)$ spans that group as a $\mathbb{Z}$-module. Let $V$ be a finitely generated free $\mathbb{Z}$-module with a $G$-representation $\rho$, and let $f : \mathrm{Rep.of}\ \rho \to P$, $g : P \to B$ be morphisms of representations with $f$ followed by $g$ equal to $0$. Fix a finite subgroup $S \le G$ and a family `cup` assigning to representations $A, B'$ of $S$ and integers $p+q=r$ a $\mathbb{Z}$-bilinear map $\hat H^p(S,A) \times \hat H^q(S,B') \to \hat H^r(S, A \otimes B')$ on Tate cohomology (group cohomology in positive degrees, $C^G/\mathrm{im}\,N$ in degree $0$, $\ker N$ in degree $-1$, group homology in degrees $\le -2$), satisfying the axioms of [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28): agreement with a graded cup product on positive degrees, naturality in both arguments, and the two compatibilities with connecting maps. Assume the short complex $(f,g)$ restricted to $S$ is short exact, and that all Tate cohomology groups of $P|_S$ vanish in every degree. Let $n, q$ be integers with $n+1+q = 2$ and let $a \in \hat H^q(S, \underline{\mathrm{Hom}}(V|_S, C|_S))$ be such that, for every $y \in \hat H^n(S, B|_S)$, the image of $\delta(y) \cup a \in \hat H^2(S, V|_S \otimes \underline{\mathrm{Hom}}(V|_S, C|_S))$ under the map induced on $\hat H^2$ by the evaluation morphism is $0$, where $\delta$ is the connecting map $\hat H^n(S,B|_S) \to \hat H^{n+1}(S, V|_S)$ of the restricted short exact sequence. Then $a = 0$.
--
--   This is the injectivity half of Tate–Nakayama duality in the form used here: the pairing $\hat H^{2-q}(S, V) \times \hat H^{q}(S, \mathrm{Hom}(V,C)) \to \hat H^2(S,C) \cong \mathbb{Z}/|S|$ is non-degenerate on the right, with the left-hand classes produced as connecting images from $\hat H^n(S,B)$ along a presentation $V \to P \to B$ with $P$ of vanishing Tate cohomology. It is used in the characterisation [`Rep.forall_map_delta_eq_zero_iff_exists_eq_sum_rho`](thm.html#Rep.forall_map_delta_eq_zero_iff_exists_eq_sum_rho).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_tateNakayamaPairing_right_eq_zero_of_shortExact.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam
import Definitions.Def_GroupCohomology_TateShiftMaps
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct
import Definitions.Def_GroupCohomology_IsTateCupProduct
import Definitions.Def_GroupCohomology_RelationModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Rep MonoidalCategory

theorem Rep.IsTateCupProduct.tateNakayamaPairing_right_eq_zero_of_shortExact {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)
    {P B : Rep ℤ G} (f : Rep.of ρ ⟶ P) (g : P ⟶ B) (w : f ≫ g = 0)
    (S : Subgroup G) [Fintype S] (cup : Rep.TateCupFamily ℤ S) (hcup : Rep.IsTateCupProduct cup)
    (hX : ((ShortComplex.mk f g w).map (Rep.resFunctor S.subtype)).ShortExact)
    (hP : ∀ q : ℤ, CategoryTheory.Limits.IsZero ((Rep.res S.subtype P).tateCohomology q))
    (n q : ℤ) (h : n + 1 + q = 2)
    (a : ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C)).tateCohomology q)
    (ha : ∀ y : (Rep.res S.subtype B).tateCohomology n,
        (Rep.tateMap ((ihom.ev (Rep.res S.subtype (Rep.of ρ))).app (Rep.res S.subtype C)) 2).hom
          (cup (Rep.res S.subtype (Rep.of ρ)) ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C)) (n + 1) q 2 h ((Rep.tateδ hX n).hom y) a) = 0) :
    a = 0 := by sorry
