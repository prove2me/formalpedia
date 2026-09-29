-- Prove2me | Theorems.Thm_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq_of_shortExact
-- name    : Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq_of_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/5e5b4909-34dd-50a8-b7e2-2ad43173695b
-- title:
--   Tate–Nakayama surjectivity via a Tate-acyclic presentation
-- statement:
--   Let $G$ be a finite group and $C$ an object of `Rep ℤ G`, together with a class $u \in H^2(G,C)$ subject to three hypotheses: for every subgroup $S \le G$ one has $H^1(S, C|_S) = 0$; for every subgroup $S$ the group $H^2(S, C|_S)$ is finite of order $|S|$; and for every subgroup $S$ the restriction of $u$ to $H^2(S, C|_S)$ spans it as a $\mathbb{Z}$-module. Let $V$ be a finitely generated free $\mathbb{Z}$-module with a $G$-representation $\rho$, and let $f : \mathrm{of}\,\rho \to P$, $g : P \to B$ be morphisms of $\mathbb{Z}[G]$-representations with $f$ followed by $g$ zero. Fix a subgroup $S \le G$ and a family `cup` assigning to representations $A, B$ of $S$ and integers $p + q = r$ a $\mathbb{Z}$-bilinear map $\hat H^p(S,A) \times \hat H^q(S,B) \to \hat H^r(S, A \otimes B)$, assumed to satisfy [`Rep.IsTateCupProduct`](def/GroupCohomology_IsTateCupProduct.html#L28): it agrees with a graded cup product on $H^{p+1} \times H^{q+1}$, is natural in both arguments under $\varphi \otimes \psi$, and commutes with the connecting maps of short exact sequences in the first variable and, up to the sign $(-1)^p$, in the second. Here Tate cohomology $\hat H^m$ means group cohomology for $m \ge 1$, invariants modulo the image of the norm for $m = 0$, the kernel of the norm on the module for $m = -1$, and group homology $H_{-m-1}$ for $m \le -2$. Assume further that restricting $f, g$ to $S$ yields a short exact sequence of representations of $S$, and that every Tate cohomology group $\hat H^m(S, P|_S)$, $m \in \mathbb{Z}$, vanishes. Then for integers $n, q$ with $n + 1 + q = 2$ and every $\mathbb{Z}$-linear map $\varphi : \hat H^n(S, B|_S) \to H^2(S, C|_S)$ there exists $a \in \hat H^q(S, \underline{\mathrm{Hom}}(V|_S, C|_S))$, the internal hom of representations of $S$, such that for all $y \in \hat H^n(S, B|_S)$ the image of $\mathrm{cup}(\delta y, a)$ under the evaluation map $V|_S \otimes \underline{\mathrm{Hom}}(V|_S, C|_S) \to C|_S$ in degree $2$ equals $\varphi(y)$, where $\delta$ is the connecting map $\hat H^n(S, B|_S) \to \hat H^{n+1}(S, V|_S)$ of the restricted sequence.
--
--   This is the surjectivity half of Tate–Nakayama duality in the form $\hat H^q(S, \mathrm{Hom}(V,C)) \to \mathrm{Hom}(\hat H^n(S,B), H^2(S,C))$, transported from free coefficients $V$ to coefficients $B$ presented by a Tate-acyclic module $P$: every functional on $\hat H^n(S,B)$ is realised by cupping with a class and evaluating. It is used in the construction of the homomorphisms out of relation modules in [`Rep.exists_hom_relationModuleInt_forall_map_delta_eq`](thm.html#Rep.exists_hom_relationModuleInt_forall_map_delta_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_IsTateCupProduct_exists_tateNakayamaPairing_right_eq_of_shortExact.lean

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

theorem Rep.IsTateCupProduct.exists_tateNakayamaPairing_right_eq_of_shortExact {G : Type} [Group G] [Fintype G]
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
    (φ : (Rep.res S.subtype B).tateCohomology n →ₗ[ℤ] groupCohomology (Rep.res S.subtype C) 2) :
    ∃ a : ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C)).tateCohomology q,
      ∀ y : (Rep.res S.subtype B).tateCohomology n,
        (Rep.tateMap ((ihom.ev (Rep.res S.subtype (Rep.of ρ))).app (Rep.res S.subtype C)) 2).hom
          (cup (Rep.res S.subtype (Rep.of ρ)) ((ihom (Rep.res S.subtype (Rep.of ρ))).obj (Rep.res S.subtype C)) (n + 1) q 2 h ((Rep.tateδ hX n).hom y) a) = φ y := by sorry
