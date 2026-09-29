-- Prove2me | Theorems.Thm_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_forall_sum_rho_eq_nsmul
-- name    : Rep.exists_comp_eq_or_exists_map_delta_ne_zero_of_forall_sum_rho_eq_nsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/14b5b44b-fa7d-53c8-b571-ddd57650da9b
-- title:
--   Extension dichotomy for maps from the integral relation module
-- statement:
--   Let $H$ be a finite group and $C$ an object of $\mathrm{Rep}\,\mathbb{Z}\,H$, i.e. a $\mathbb{Z}[H]$-module, and let $u \in H^2(H,C)$. Assume the class-formation hypotheses at every subgroup $S \le H$: the group $H^1(S, C)$ (cohomology of the restriction of $C$ along $S \hookrightarrow H$) is a zero object; for $S$ finite, $H^2(S,C)$ has cardinality $|S|$; and the restriction of $u$ to $H^2(S,C)$ spans $H^2(S,C)$ as a $\mathbb{Z}$-module. Let $p$ be a prime and assume that for every $c \in C$ there is a $d \in C$ fixed by all $\rho(g)$, $g \in H$, with $\sum_{g \in H} \rho(g)c = p\,d$. Let $B_0$ be a finite object of $\mathrm{Rep}\,\mathbb{Z}\,H$ with $p\,b = 0$ for all $b \in B_0$ and with trivial $H$-action. Assume the short complex $\mathrm{relationSeqInt}\,B_0$, formed by the inclusion $\iota$ of the integral relation module $\mathrm{relationModuleInt}\,B_0$ followed by the canonical map $\mathrm{freeCover}\,B_0 : \mathrm{Rep.free}\,\mathbb{Z}\,H\,B_0 \to B_0$ sending each basis element $b$ to $b$, is short exact; call this hypothesis $hX$. Then for every morphism $\varphi : \mathrm{relationModuleInt}\,B_0 \to C$ of representations, either $\varphi$ factors as $\iota$ followed by some $\chi : \mathrm{Rep.free}\,\mathbb{Z}\,H\,B_0 \to C$, or there is a $y \in H^1(H,B_0)$ whose image under the connecting map $\delta : H^1(H,B_0) \to H^2(H, \mathrm{relationModuleInt}\,B_0)$ attached to $hX$, followed by the map induced by $\varphi$, is non-zero in $H^2(H,C)$.
--
--   This is the finite-level dichotomy used in the class-formation (Herbrand-quotient) part of the argument: an equivariant map out of the relation module of a presentation of $B_0$ either extends to the free cover, or is detected by a non-trivial obstruction class coming from $H^1(H,B_0)$ through the connecting homomorphism. It is invoked in the construction of a level at which homomorphisms from the relation module into the $S$-idèle class group extend, namely [`M4aHerbrand.exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero`](thm.html#M4aHerbrand.exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_forall_sum_rho_eq_nsmul.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand ExtCitation

theorem Rep.exists_comp_eq_or_exists_map_delta_ne_zero_of_forall_sum_rho_eq_nsmul
    {H : Type} [Group H] [Fintype H] [DecidableEq H]
    (C : Rep ℤ H) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup H), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup H) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup H),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (p : ℕ) [Fact p.Prime]
    (hnorm : ∀ c : C, ∃ d : C, (∀ g : H, C.ρ g d = d) ∧ (∑ g : H, C.ρ g c) = p • d)
    (B₀ : Rep ℤ H) [Fintype B₀] (hB₀ : ∀ b : B₀, p • b = 0) (htriv : ∀ (g : H) (b : B₀), B₀.ρ g b = b)
    (hX : (Rep.relationSeqInt B₀).ShortExact) (φ : Rep.relationModuleInt B₀ ⟶ C) :
    (∃ χ : Rep.free ℤ H B₀ ⟶ C, Rep.relationModuleInt.ι B₀ ≫ χ = φ) ∨
    (∃ y : groupCohomology B₀ 1,
      (groupCohomology.map (MonoidHom.id H) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y) ≠ 0) := by sorry
