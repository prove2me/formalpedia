-- Prove2me | Theorems.Thm_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top
-- name    : Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/291882c4-7a98-5782-97a4-cc12b9c59d5a
-- title:
--   Eigenvalues on a lattice-preserving family are integral
-- statement:
--   Let $V$ be a finite-dimensional complex vector space, let $\Lambda \subseteq V$ be a $\mathbb{Z}$-submodule which is finitely generated (`Λ.FG`) and whose $\mathbb{C}$-span is all of $V$, let $J$ be an arbitrary index type and let $S : J \to \operatorname{End}_{\mathbb{C}}(V)$ be a family of $\mathbb{C}$-linear endomorphisms of $V$ with $S_j x \in \Lambda$ for every $j \in J$ and every $x \in \Lambda$. Suppose given scalars $\lambda : J \to \mathbb{C}$ and a vector $v \in V$ with $v \neq 0$ such that $S_j v = \lambda_j \cdot v$ for all $j \in J$, so that $v$ is a common eigenvector of the family with eigenvalue $\lambda_j$ for $S_j$. The conclusion is that the $\mathbb{Z}$-subalgebra $\mathbb{Z}[\lambda_j : j \in J]$ of $\mathbb{C}$, namely `Algebra.adjoin ℤ (Set.range lam)`, is a finite $\mathbb{Z}$-module. In particular each $\lambda_j$ is an algebraic integer, although the statement as formalised is the finiteness of the whole generated ring rather than integrality of individual eigenvalues.
--
--   This is the abstract form of the classical argument that Hecke eigenvalues of a modular form whose Fourier coefficients lie in a finitely generated spanning subgroup are algebraic integers (Shimura, Theorem 3.48; Deligne–Serre (2.7.1)–(2.7.3)). It is used in the weight-one Deligne–Serre construction, specifically by [`DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen`](thm.html#DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Λ : Submodule ℤ V) (hΛfg : Λ.FG) (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤)
    {J : Type*} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ)
    (lam : J → ℂ) (v : V) (hv0 : v ≠ 0) (hv : ∀ j : J, S j v = lam j • v) :
    Module.Finite ℤ (Algebra.adjoin ℤ (Set.range lam)) := by sorry
