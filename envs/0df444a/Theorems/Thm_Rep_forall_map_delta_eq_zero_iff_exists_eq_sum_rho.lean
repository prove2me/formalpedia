-- Prove2me | Theorems.Thm_Rep_forall_map_delta_eq_zero_iff_exists_eq_sum_rho
-- name    : Rep.forall_map_delta_eq_zero_iff_exists_eq_sum_rho
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/ff22b02d-67ee-544e-9414-6b4648bcea39
-- title:
--   Vanishing of φ_*∘δ iff φ is a G-norm
-- statement:
--   Let $G$ be a finite group, let $C$ be a $\mathbb{Z}[G]$-representation and let $u \in H^2(G,C)$ be such that for every subgroup $S \le G$: the group $H^1(S, C)$ (cohomology of the restriction of $C$ along the inclusion $S \hookrightarrow G$) is a zero object, the cardinality of $H^2(S,C)$ equals $|S|$, and the $\mathbb{Z}$-span of the image of $u$ under restriction to $H^2(S,C)$ is everything. Let $B$ be a $\mathbb{Z}[G]$-representation whose underlying type is finite, and assume the short complex $0 \to R(B) \to \mathbb{Z}[G]^{(B)} \to B$ is short exact, where $\mathbb{Z}[G]^{(B)}$ is the free representation on the underlying set of $B$, the second map is the canonical lift of the identity on $B$, and $R(B)$ is its kernel, regarded as a representation over $\mathbb{Z}$ with the inherited action. Let $\varphi \colon R(B) \to C$ be $G$-equivariant. Then $\varphi_*(\delta y) = 0$ in $H^2(G,C)$ for every $y \in H^1(G,B)$, where $\delta \colon H^1(G,B) \to H^2(G,R(B))$ is the connecting map of the above short exact sequence, if and only if there is an additive map $\psi \colon R(B) \to C$, not assumed equivariant, with $\varphi(x) = \sum_{g \in G} \rho_C(g)\,\psi(g^{-1}x)$ for all $x \in R(B)$.
--
--   This is the kernel computation for the degree-one map $\varphi \mapsto (y \mapsto \varphi_*(\delta y))$ attached to a class module $(C,u)$ in the Tate–Nakayama framework: the equivariant maps $R(B) \to C$ annihilating the image of the connecting homomorphism are exactly the $G$-norms of additive maps. It is used by [`Rep.exists_comp_eq_or_exists_map_delta_ne_zero_of_forall_sum_rho_eq_nsmul`](thm.html#Rep.exists_comp_eq_or_exists_map_delta_ne_zero_of_forall_sum_rho_eq_nsmul) and by [`Rep.exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective`](thm.html#Rep.exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_forall_map_delta_eq_zero_iff_exists_eq_sum_rho.lean

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem Rep.forall_map_delta_eq_zero_iff_exists_eq_sum_rho {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (B : Rep ℤ G) [Fintype B] (hX : (Rep.relationSeqInt B).ShortExact)
    (φ : Rep.relationModuleInt B ⟶ C) :
    (∀ y : groupCohomology B 1,
        (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y) = 0) ↔
      ∃ ψ : Rep.relationCarrier B →+ C,
        ∀ x : Rep.relationModuleInt B, φ.hom x = ∑ g : G, C.ρ g (ψ (Rep.relationRepInt B g⁻¹ x)) := by sorry
