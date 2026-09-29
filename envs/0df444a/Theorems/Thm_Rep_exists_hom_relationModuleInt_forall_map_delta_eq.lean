-- Prove2me | Theorems.Thm_Rep_exists_hom_relationModuleInt_forall_map_delta_eq
-- name    : Rep.exists_hom_relationModuleInt_forall_map_delta_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/98f0aad8-14cc-5731-b8f4-b57ba6ee36ec
-- title:
--   Every map H¹(G,B)→ H²(G,C) factors through δ
-- statement:
--   Let $G$ be a finite group and let $C$ be an object of $\mathrm{Rep}\,\mathbb{Z}\,G$, i.e. a $\mathbb{Z}[G]$-module, together with a class $u \in H^2(G,C)$. Assume: for every subgroup $S \le G$ the group $H^1(S, C|_S)$ is a zero object; for every subgroup $S$ (finite) the cardinality of $H^2(S, C|_S)$ equals the order of $S$; and for every subgroup $S$ the restriction of $u$ along $S \hookrightarrow G$ (the map induced in degree $2$ by $S.\mathrm{subtype}$ together with the identity of $C|_S$) spans $H^2(S, C|_S)$ as a $\mathbb{Z}$-module, i.e. its $\mathbb{Z}$-span is the whole module. Let $B$ be an object of $\mathrm{Rep}\,\mathbb{Z}\,G$ with finite underlying type, and let `hX` assert that the short complex [`Rep.relationSeqInt B`](def/GroupCohomology_RelationModule.html#L84) is short exact; this complex is $R(B) \to \mathbb{Z}[G]^{(B)} \to B$, where the second map `freeCover` is the $G$-map from the free representation on the underlying set of $B$ sending the basis vector at $b$ to $b$, and $R(B) =$ [`Rep.relationModuleInt B`](def/GroupCohomology_RelationModule.html#L73) is the relation module [`Rep.relationCarrier B`](def/GroupCohomology_RelationModule.html#L50) with the $G$-action coming from `relationModule B`, mapping into $\mathbb{Z}[G]^{(B)}$ by the inclusion `relationModuleInt.ι`. Let $\theta : H^1(G,B) \to H^2(G,C)$ be any homomorphism of additive groups. Then there exists a morphism $\varphi : R(B) \to C$ of $\mathbb{Z}[G]$-modules such that for every $y \in H^1(G,B)$ one has $\varphi_*(\delta y) = \theta(y)$, where $\delta : H^1(G,B) \to H^2(G,R(B))$ is the connecting map of `hX` in degrees $1 \to 2$ and $\varphi_*$ is the map induced by $\varphi$ (along the identity of $G$) in degree $2$.
--
--   The hypotheses on $(C,u)$ say that $C$ is a class module for $G$ in the sense of class field theory, and the conclusion is the surjectivity half of Tate's description of $\mathrm{Hom}(H^1(G,B),H^2(G,C))$ by $\mathbb{Z}[G]$-maps out of the relation module of a finite coefficient module $B$, obtained from Tate–Nakayama duality applied to the canonical free presentation of $B$. It is used in the construction of auxiliary levels for the Herbrand-quotient computation and in the proof that the pairing between the degree-one and degree-two Shafarevich–Tate groups of a dual twist is nondegenerate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_hom_relationModuleInt_forall_map_delta_eq.lean

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem Rep.exists_hom_relationModuleInt_forall_map_delta_eq {G : Type} [Group G] [Fintype G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (B : Rep ℤ G) [Fintype B] (hX : (Rep.relationSeqInt B).ShortExact)
    (θ : groupCohomology B 1 →+ groupCohomology C 2) :
    ∃ φ : Rep.relationModuleInt B ⟶ C, ∀ y : groupCohomology B 1,
      (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y) = θ y := by sorry
