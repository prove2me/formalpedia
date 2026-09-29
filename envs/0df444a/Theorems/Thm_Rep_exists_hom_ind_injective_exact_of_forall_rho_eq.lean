-- Prove2me | Theorems.Thm_Rep_exists_hom_ind_injective_exact_of_forall_rho_eq
-- name    : Rep.exists_hom_ind_injective_exact_of_forall_rho_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/34a75aa5-b1c1-5998-93e8-87fa2dbf1575
-- title:
--   Embedding B into Ind_N^G B with p-torsion cokernel
-- statement:
--   Let $G$ be a finite group (in the smallest universe), $N$ a normal subgroup of $G$, and $B$ an object of `Rep ℤ G`, i.e. a $\mathbb{Z}[G]$-module, whose underlying type is finite. Let $p$ be a natural number such that $p \cdot b = 0$ for every $b \in B$, and assume that $N$ acts trivially on $B$, i.e. $B.\rho(g)(b) = b$ for all $g \in N$ and $b \in B$. The assertion is the existence of a morphism $\iota \colon B \to (\mathrm{Ind}_{N}^{G})(\mathrm{Res}_{N} B)$ of $\mathbb{Z}[G]$-modules, where the induced module is formed by Mathlib's `Rep.indFunctor ℤ N.subtype` applied to the restriction of $B$ along the inclusion $N \hookrightarrow G$, together with an object $B_1$ of `Rep ℤ G` with finite underlying type and a morphism $\rho \colon (\mathrm{Ind}_{N}^{G})(\mathrm{Res}_{N} B) \to B_1$, such that: the underlying map of $\iota$ is injective; the pair of underlying maps of $\iota$ and $\rho$ is exact in the sense of `Function.Exact`, i.e. the kernel of $\rho$ is exactly the image of $\iota$; $\rho$ is surjective; $p \cdot b = 0$ for every $b \in B_1$; $N$ acts trivially on $B_1$; and $N$ acts trivially on $(\mathrm{Ind}_{N}^{G})(\mathrm{Res}_{N} B)$. The number $p$ is not assumed prime.
--
--   This is the pure-algebra input producing the short exact sequence $0 \to B \to \operatorname{Ind}_N^G(B|_N) \to B_1 \to 0$ of finite $p$-torsion $\mathbb{Z}[G]$-modules on which $N$ acts trivially, used when a cohomological statement about $B$ is reduced by dévissage to the induced module and to a module of the same shape. It is cited in the construction of relation-module homomorphisms into $S$-idele class groups, in [`M4aHerbrand.exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero`](thm.html#M4aHerbrand.exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_exists_hom_ind_injective_exact_of_forall_rho_eq.lean

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

theorem Rep.exists_hom_ind_injective_exact_of_forall_rho_eq
    {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal] (B : Rep ℤ G) [Fintype B] (p : ℕ) (hB : ∀ b : B, p • b = 0)
    (hN : ∀ g ∈ N, ∀ b : B, B.ρ g b = b) :
    ∃ (ι : B ⟶ (Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B)) (B₁ : Rep ℤ G) (_ : Fintype B₁)
      (ρ : (Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B) ⟶ B₁),
      Function.Injective ι.hom ∧ Function.Exact ι.hom ρ.hom ∧ Function.Surjective ρ.hom ∧
      (∀ b : B₁, p • b = 0) ∧ (∀ g ∈ N, ∀ b : B₁, B₁.ρ g b = b) ∧
      (∀ g ∈ N, ∀ x : (Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B), ((Rep.indFunctor ℤ N.subtype).obj (Rep.res N.subtype B)).ρ g x = x) := by sorry
