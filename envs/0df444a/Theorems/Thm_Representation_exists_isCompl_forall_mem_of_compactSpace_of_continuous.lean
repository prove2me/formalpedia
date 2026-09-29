-- Prove2me | Theorems.Thm_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous
-- name    : Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/b44684ad-8138-59f5-8d42-f5ddfc0ed4c0
-- title:
--   Stable complements for continuous representations of compact groups
-- statement:
--   Let $H$ be a group carrying a topology making it a topological group which is compact, and let $E$ be a finite-dimensional complex vector space. Let $\pi : H \to \mathrm{End}_{\mathbb C}(E)$ be a representation of $H$ on $E$ over $\mathbb{C}$ (a monoid homomorphism into the endomorphisms of $E$), and assume its matrix coefficients are continuous, in the sense that for every linear form $\ell$ on $E$ and every $v \in E$ the function $k \mapsto \ell(\pi(k)v)$ is continuous on $H$. Let $P \subseteq E$ be a $\mathbb{C}$-submodule which is stable: $\pi(k)v \in P$ for all $k \in H$ and all $v \in P$. The conclusion asserts the existence of a $\mathbb{C}$-submodule $P^{c} \subseteq E$ which is a complement of $P$ (their infimum is trivial and their supremum is all of $E$) and which is likewise stable: $\pi(k)v \in P^{c}$ for all $k \in H$ and all $v \in P^{c}$. No measurable structure on $H$ is assumed in the statement.
--
--   This is complete reducibility (Maschke's averaging argument, in the form used for compact groups) for finite-dimensional representations with continuous matrix coefficients. It is used in the treatment of automorphic forms, where the action of a compact group on a finite-dimensional space of translates must be split into invariant pieces; it is cited, among others, by [`AutomorphicForm.exists_linearMap_archCutProjector_comm_rightTranslate`](thm.html#AutomorphicForm.exists_linearMap_archCutProjector_comm_rightTranslate) and [`AutomorphicForm.exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates`](thm.html#AutomorphicForm.exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open MeasureTheory

theorem Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    {E : Type v} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (π : Representation ℂ H E) (hπ : ∀ (ℓ : Module.Dual ℂ E) (v : E), Continuous fun k => ℓ (π k v))
    (P : Submodule ℂ E) (hP : ∀ k : H, ∀ v ∈ P, π k v ∈ P) :
    ∃ Pc : Submodule ℂ E, IsCompl P Pc ∧ ∀ k : H, ∀ v ∈ Pc, π k v ∈ Pc := by sorry
