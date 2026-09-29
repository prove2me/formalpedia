-- Prove2me | Theorems.Thm_WLight_exists_twist_of_flat
-- name    : WLight.exists_twist_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/a326dd6d-205b-5b37-a3dc-7dbb79f3f473
-- title:
--   Coordinate twist on the span of a flat K-structure
-- statement:
--   Let $K$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{C}$ and let $M$ be a $K$-submodule of the space $\mathbb{H} \to \mathbb{C}$ of all complex-valued functions on the upper half-plane. Assume the flatness hypothesis: for every finite set $s$ of functions $\mathbb{H} \to \mathbb{C}$ contained in $M$, if the family of elements of $s$ (indexed by $s$ itself) is linearly independent over $K$, then it is linearly independent over $\mathbb{C}$. Let $\sigma$ be an automorphism of $\mathbb{C}$ as a $K$-algebra, i.e. a field automorphism of $\mathbb{C}$ fixing $K$ pointwise. The conclusion asserts the existence of a function $T \colon (\mathbb{H} \to \mathbb{C}) \to (\mathbb{H} \to \mathbb{C})$ — merely a map of sets, with no linearity or continuity asserted — such that for every finite index type $\iota$, every family of complex scalars $c \colon \iota \to \mathbb{C}$ and every family of functions $e \colon \iota \to (\mathbb{H} \to \mathbb{C})$ with $e_i \in M$ for all $i$, one has $T\big(\sum_i c_i e_i\big) = \sum_i \sigma(c_i)\, e_i$. Nothing is asserted about the values of $T$ outside the $\mathbb{C}$-span of $M$.
--
--   The operator $T$ is the twisting of coordinates by $\sigma$ with respect to a $K$-structure $M$ inside the functions on $\mathbb{H}$: its well-definedness is exactly the descent of $\mathbb{C}$-linear relations among elements of $M$ to $K$-linear relations, which the flatness hypothesis provides. It is used in the rationality arguments for spaces of modular and cusp forms, namely in [`ModularForm.span_frickeRational_E4_pow_E6_pow_eq_top`](thm.html#ModularForm.span_frickeRational_E4_pow_E6_pow_eq_top) and [`CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top`](thm.html#CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top), where the $K$-structure is given by forms with rational $q$-expansion coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WLight_exists_twist_of_flat.lean

import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Complex UpperHalfPlane Function
open scoped Topology Manifold ModularForm

theorem WLight.exists_twist_of_flat (K : IntermediateField ℚ ℂ) (M : Submodule ↥K (ℍ → ℂ))
    (hflat : ∀ s : Finset (ℍ → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) →
      LinearIndependent ↥K (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) →
      LinearIndependent ℂ (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)))
    (σ : ℂ ≃ₐ[↥K] ℂ) :
    ∃ T : (ℍ → ℂ) → (ℍ → ℂ), ∀ (ι : Type) [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ),
      (∀ i, e i ∈ M) → T (∑ i, c i • e i) = ∑ i, σ (c i) • e i := by sorry
