-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq
-- name    : Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/91a41c2d-2160-5b54-b282-b5cd2893b8e9
-- title:
--   Tate–Nakayama pairing: surjectivity in the right variable
-- statement:
--   Let $G$ be a finite group, let $C$ be a representation of $G$ over $\mathbb{Z}$ and let $u \in H^2(G,C)$ be a class such that, for every subgroup $S \le G$: the group $H^1(S, C)$ of the restriction of $C$ along the inclusion $S \hookrightarrow G$ is a zero object, the cardinality of $H^2(S,C)$ equals $|S|$ whenever $S$ is given a finite type structure, and $H^2(S,C)$ is spanned over $\mathbb{Z}$ by the image of $u$ under restriction. Let $V$ be a finite free $\mathbb{Z}$-module with a $\mathbb{Z}$-linear $G$-representation $\rho$, write $M = \mathrm{Rep.of}\ \rho$, let $S \le G$ be a finite subgroup, and let `cup` be a family of $\mathbb{Z}$-bilinear maps $\hat H^p(S,A) \times \hat H^q(S,B) \to \hat H^r(S, A \otimes B)$, defined for all representations $A,B$ of $S$ and all integers $p+q=r$, satisfying the axioms of [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28): agreement in strictly positive degrees with any graded cup product on group cohomology, naturality in both variables, and the two compatibilities with connecting maps for short exact sequences tensored on the right and on the left (the latter up to the sign $(-1)^p$). Here $\hat H^n$ denotes Tate cohomology as defined by cases: group cohomology $H^n$ for $n \ge 1$, the invariants modulo the image of the normalised norm for $n = 0$, the kernel of that norm for $n = -1$, and group homology $H_{-n-1}$ for $n \le -2$. Finally let $q$ be an integer and let $\varphi \colon \hat H^{2-q}(S, M) \to H^2(S, C)$ be $\mathbb{Z}$-linear. Then there exists a class $a \in \hat H^{q}\big(S, \underline{\mathrm{Hom}}(M, C)\big)$, the internal hom of the restrictions to $S$, such that for every $x \in \hat H^{2-q}(S,M)$ the image of $\mathrm{cup}(x, a) \in \hat H^2\big(S, M \otimes \underline{\mathrm{Hom}}(M,C)\big)$ under the map induced in degree $2$ by the evaluation $\underline{\mathrm{Hom}}(M,C) \otimes$-counit $\mathrm{ev} \colon M \otimes \underline{\mathrm{Hom}}(M,C) \to C$ equals $\varphi(x)$.
--
--   This is the surjectivity half of the non-degeneracy of the Tate–Nakayama pairing $\langle x, a\rangle = \mathrm{ev}_*(x \cup a)$ between $\hat H^{2-q}(S,M)$ and $\hat H^{q}(S,\underline{\mathrm{Hom}}(M,C))$ with values in $H^2(S,C) \cong \mathbb{Z}/|S|$, in the axiomatic setting of a class formation datum $(C,u)$. It feeds the variant for short exact sequences, [`Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq_of_shortExact`](thm.html#Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq_of_shortExact), used in the local and global duality input to the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq.lean

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

theorem Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (V : Type) [AddCommGroup V] [Module.Free ℤ V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)
    (S : Subgroup G) [Fintype S] (cup : Rep.TateCupFamily ℤ S) (hcup : Rep.IsTateCupProduct cup) (q : ℤ)
    (φ : (Rep.res S.subtype (Rep.of ρ)).tateCohomology (2 - q) →ₗ[ℤ] groupCohomology (Rep.res S.subtype C) 2) :
    ∃ a : ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C)).tateCohomology q,
      ∀ x : (Rep.res S.subtype (Rep.of ρ)).tateCohomology (2 - q),
        (Rep.tateMap ((ihom.ev (Rep.res S.subtype (Rep.of ρ))).app (Rep.res S.subtype C)) 2).hom
          (cup (Rep.res S.subtype (Rep.of ρ)) ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C))
            (2 - q) q 2 (by omega) x a) = φ x := by sorry
