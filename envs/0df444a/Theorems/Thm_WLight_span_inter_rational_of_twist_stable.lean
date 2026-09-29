-- Prove2me | Theorems.Thm_WLight_span_inter_rational_of_twist_stable
-- name    : WLight.span_inter_rational_of_twist_stable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/d39a485e-2921-5426-83f9-b670f28f106f
-- title:
--   Galois descent for twist-stable subspaces of functions H→ℂ
-- statement:
--   Let $K$ be an intermediate field of $\mathbb{Q}\subseteq\mathbb{C}$, and let $M$ be a $K$-submodule of the space of all functions $\mathbb{H}\to\mathbb{C}$ (no continuity or holomorphy is involved). Assume the flatness hypothesis `hflat`: every finite subset $s$ of $M$ that is linearly independent over $K$ is also linearly independent over $\mathbb{C}$. Let $V$ be a $\mathbb{C}$-subspace of $\mathbb{H}\to\mathbb{C}$ contained in the $\mathbb{C}$-span of $M$. Assume the twist-stability hypothesis `hstab`: for every $K$-algebra automorphism $\sigma$ of $\mathbb{C}$ and every $v\in V$ there exist a finite subset $s\subseteq M$ and a coefficient function $c$ on $\mathbb{H}\to\mathbb{C}$ with values in $\mathbb{C}$ such that $v=\sum_{w\in s}c_w\,w$ and the twisted combination $\sum_{w\in s}\sigma(c_w)\,w$ again lies in $V$. Assume the fixed-field hypothesis `G1`: every $c\in\mathbb{C}$ fixed by all $K$-algebra automorphisms of $\mathbb{C}$ is in the image of $K\to\mathbb{C}$. Then every $v\in V$ lies in the $\mathbb{C}$-span of the set of functions belonging both to $V$ and to $M$.
--
--   This is a Galois-descent statement at the level of bare functions on the upper half-plane: a twist-stable complex subspace of the span of a $K$-structure is spanned by its $K$-rational vectors. It is applied, with $K$ a cyclotomic field and $M$ a space of forms with rational Fourier coefficients, in the proofs that the Fricke-rational modular and cusp forms span, namely [`ModularForm.span_frickeRational_E4_pow_E6_pow_eq_top`](thm.html#ModularForm.span_frickeRational_E4_pow_E6_pow_eq_top) and [`CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top`](thm.html#CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WLight_span_inter_rational_of_twist_stable.lean

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

theorem WLight.span_inter_rational_of_twist_stable (K : IntermediateField ℚ ℂ)
    (M : Submodule ↥K (ℍ → ℂ))
    (hflat : ∀ s : Finset (ℍ → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) →
      LinearIndependent ↥K (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) →
      LinearIndependent ℂ (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)))
    (V : Submodule ℂ (ℍ → ℂ))
    (hVle : V ≤ Submodule.span ℂ (M : Set (ℍ → ℂ)))
    (hstab : ∀ (σ : ℂ ≃ₐ[↥K] ℂ) (v : ℍ → ℂ), v ∈ V →
      ∃ (s : Finset (ℍ → ℂ)) (c : (ℍ → ℂ) → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) ∧
        v = ∑ w ∈ s, c w • w ∧ (∑ w ∈ s, σ (c w) • w) ∈ V)
    (G1 : ∀ c : ℂ, (∀ σ : ℂ ≃ₐ[↥K] ℂ, σ c = c) → ∃ a : ↥K, algebraMap ↥K ℂ a = c)
    {v : ℍ → ℂ} (hv : v ∈ V) :
    v ∈ Submodule.span ℂ {y : ℍ → ℂ | y ∈ V ∧ y ∈ M} := by sorry
