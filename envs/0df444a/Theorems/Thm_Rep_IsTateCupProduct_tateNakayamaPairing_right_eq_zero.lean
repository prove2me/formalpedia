-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_tateNakayamaPairing_right_eq_zero
-- name    : Rep.IsTateCupProduct.tateNakayamaPairing_right_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/965e952a-945c-5f60-bfa2-f8ef23fe1e7c
-- title:
--   Right non-degeneracy of the Tate–Nakayama pairing
-- statement:
--   Let $G$ be a finite group and $C$ an object of $\mathrm{Rep}\,\mathbb{Z}\,G$, and let $u \in H^2(G, C)$. Assume that for every subgroup $S \le G$ the module $H^1(S, C)$ (cohomology of the restriction of $C$ along the inclusion $S \hookrightarrow G$) is a zero object, that for every finite subgroup $S$ one has $\#H^2(S, C) = \#S$, and that for every $S$ the $\mathbb{Z}$-span of the single element obtained from $u$ by restriction to $S$ in degree $2$ is all of $H^2(S, C)$. Let $V$ be a free, finitely generated $\mathbb{Z}$-module with a $G$-action $\rho$, let $S \le G$ be a subgroup with a finiteness instance, and let $cup$ be a family of $\mathbb{Z}$-bilinear maps $\hat H^p(S,A) \times \hat H^q(S,B) \to \hat H^r(S, A \otimes B)$ for all $p + q = r$ satisfying [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28) (compatibility with graded cup products in strictly positive degrees, naturality in both arguments, and the two compatibilities with connecting maps of short exact sequences). Here Tate cohomology $\hat H^n$ is group cohomology for $n > 0$, invariants modulo the image of the norm for $n = 0$, the kernel of the norm on coinvariants for $n = -1$, and group homology for $n < -1$. Finally let $q \in \mathbb{Z}$ and let $a \in \hat H^q\bigl(S, \underline{\mathrm{Hom}}(M, C)\bigr)$, where $M = \mathrm{Rep.of}\ \rho$ restricted to $S$, $C$ is restricted to $S$, and $\underline{\mathrm{Hom}}$ is the internal hom of $\mathrm{Rep}\,\mathbb{Z}\,S$. Assume that for every $x \in \hat H^{2-q}(S, M)$ the class $\mathrm{ev}_*(x \cup a) \in \hat H^2(S, C) = H^2(S, C)$ vanishes, where $\mathrm{ev} \colon M \otimes \underline{\mathrm{Hom}}(M, C) \to C$ is the evaluation morphism and $\mathrm{ev}_*$ is the induced map on Tate cohomology in degree $2$. Then $a = 0$.
--
--   This is one half of the perfectness of the Tate–Nakayama pairing $\hat H^{2-q}(S, M) \times \hat H^{q}(S, \underline{\mathrm{Hom}}(M,C)) \to H^2(S,C)$ attached to a class $u$ whose restrictions are fundamental classes, stated as the implication that a class pairing to zero against everything vanishes. It is used, together with surjectivity statements for the same pairing, in the duality input to the Tate–Nakayama and Poitou–Tate style arguments, and is invoked by the corresponding statement for short exact sequences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_tateNakayamaPairing_right_eq_zero.lean

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

theorem Rep.IsTateCupProduct.tateNakayamaPairing_right_eq_zero {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)
    (S : Subgroup G) [Fintype S] (cup : Rep.TateCupFamily ℤ S) (hcup : Rep.IsTateCupProduct cup) (q : ℤ)
    (a : ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C)).tateCohomology q)
    (ha : ∀ x : (Rep.res S.subtype (Rep.of ρ)).tateCohomology (2 - q),
      (Rep.tateMap ((ihom.ev (Rep.res S.subtype (Rep.of ρ))).app (Rep.res S.subtype C)) 2).hom
        (cup (Rep.res S.subtype (Rep.of ρ)) ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C))
          (2 - q) q 2 (by omega) x a) = 0) :
    a = 0 := by sorry
