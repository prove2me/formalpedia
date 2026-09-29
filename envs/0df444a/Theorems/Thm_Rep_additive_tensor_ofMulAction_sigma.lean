-- Prove2me | Theorems.Thm_Rep_additive_tensor_ofMulAction_sigma
-- name    : Rep.additive_tensor_ofMulAction_sigma
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/fc4518ba-77a4-5908-a25d-10c13c6f7d28
-- title:
--   Additivity of ψ over disjoint unions of finite G-sets
-- statement:
--   Let $k$ be a field and $G$ a group, and let $\psi$ be a $\mathbb{Z}$-valued function on the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$ (in the lowest universe). Assume $\psi$ is additive in the following sense: for every short complex $X_1 \to X_2 \to X_3$ of representations that is short exact and whose middle term $X_2$ is finite-dimensional over $k$, one has $\psi(X_2) = \psi(X_1) + \psi(X_3)$. Let $M$ be a representation that is finite-dimensional over $k$, let $\iota$ be a finite index type, and let $(X_i)_{i \in \iota}$ be a family of types, each carrying a $G$-action and each finite. For a $G$-set $H$ write $\mathrm{Rep.ofMulActionFinsupp}\,k\,G\,H$ for the permutation representation on the finitely supported functions $H \to_{0} k$, with $g \in G$ acting by pushing forward supports along $h \mapsto g \cdot h$. Then, with $\otimes$ the monoidal tensor product of $\mathrm{Rep}\,k\,G$, $$\psi\bigl(M \otimes k[\textstyle\coprod_{i} X_i]\bigr) = \sum_{i \in \iota} \psi\bigl(M \otimes k[X_i]\bigr),$$ where $\coprod_i X_i$ denotes the dependent sum $\Sigma\, i,\ X_i$ with its componentwise $G$-action.
--
--   This records that an additive $\mathbb{Z}$-valued invariant of finite-dimensional representations, evaluated on a fixed finite-dimensional representation twisted by a permutation module, is additive over disjoint unions of finite $G$-sets, the underlying isomorphisms being $k[\coprod_i X_i] \cong \bigoplus_i k[X_i]$ and the distribution of $M \otimes -$ over finite direct sums. It is used in the evaluation of $\psi$ on the virtual permutation-twisted modules occurring in Artin's induction identity, in the proof of [`Rep.eq_zero_of_additive_of_forall_ind_isCyclic_coprime`](thm.html#Rep.eq_zero_of_additive_of_forall_ind_isCyclic_coprime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_additive_tensor_ofMulAction_sigma.lean

import Mathlib
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical

theorem Rep.additive_tensor_ofMulAction_sigma
    {k : Type} [Field k] {G : Type} [Group G]
    (ψ : Rep.{0} k G → ℤ)
    (hadd : ∀ (X : ShortComplex (Rep.{0} k G)), X.ShortExact →
      FiniteDimensional k X.X₂ → ψ X.X₂ = ψ X.X₁ + ψ X.X₃)
    (M : Rep.{0} k G) [FiniteDimensional k M]
    {ι : Type} [Fintype ι] (X : ι → Type) [∀ i, MulAction G (X i)] [∀ i, Finite (X i)] :
    ψ (M ⊗ Rep.ofMulActionFinsupp k G (Σ i, X i)) = ∑ i, ψ (M ⊗ Rep.ofMulActionFinsupp k G (X i)) := by sorry
