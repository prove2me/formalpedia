-- Prove2me | Theorems.Thm_Submodule_finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite
-- name    : Submodule.finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/3d539345-a492-50ed-90ee-9f1cced4e9fc
-- title:
--   Bounded orthonormal families force dim V ≤ D
-- statement:
--   Let $E$ be a complex vector space (an additive commutative group with a $\mathbb{C}$-module structure), let $V$ be a $\mathbb{C}$-submodule of $E$, and let $B : E \times E \to \mathbb{C}$ be a function satisfying: additivity in the first variable, $B(x+y,z) = B(x,z)+B(y,z)$ for all $x,y,z$; homogeneity in the first variable, $B(c \cdot x, y) = c\,B(x,y)$ for all $c \in \mathbb{C}$ and all $x,y$; Hermitian symmetry, $B(y,x) = \overline{B(x,y)}$ for all $x,y$; positivity on $V$, $\operatorname{Re} B(x,x) \ge 0$ for every $x \in V$; and definiteness on $V$, $B(x,x) = 0$ with $x \in V$ implies $x = 0$. Let $D$ be a natural number such that for every $n$ and every family $e : \mathrm{Fin}\,n \to E$ with all $e_i \in V$ and $B(e_i,e_j) = \delta_{ij}$ (that is, $1$ if $i = j$ and $0$ otherwise), one has $n \le D$. The conclusion is the conjunction: $V$ is finite-dimensional over $\mathbb{C}$, and $\operatorname{finrank}_{\mathbb{C}} V \le D$. Note that positivity and definiteness, as well as the bound on orthonormal families, are only required for vectors lying in $V$, while additivity, homogeneity and Hermitian symmetry are required on all of $E$.
--
--   This is the standard dimension bound for a definite Hermitian form admitting no long orthonormal families; it is pure linear algebra, formulated so that the form is given as a raw function on an ambient space $E$ and only assumed positive definite on the subspace $V$. It is used in the analytic part of the argument, in the proof that induced sections at a principal level have finite-dimensional spaces of archimedean cut-offs invariant under a maximal compact subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ComplexConjugate

theorem Submodule.finiteDimensional_and_finrank_le_of_forall_orthonormal_card_le_of_definite
    {E : Type*} [AddCommGroup E] [Module ℂ E] (V : Submodule ℂ E)
    (B : E → E → ℂ)
    (hadd : ∀ x y z, B (x + y) z = B x z + B y z)
    (hsmul : ∀ (c : ℂ) (x y : E), B (c • x) y = c * B x y)
    (hsymm : ∀ x y, B y x = conj (B x y))
    (hpos : ∀ x ∈ V, 0 ≤ (B x x).re)
    (hdef : ∀ x ∈ V, B x x = 0 → x = 0)
    (D : ℕ) (hD : ∀ (n : ℕ) (e : Fin n → E), (∀ i, e i ∈ V) →
      (∀ i j, B (e i) (e j) = if i = j then 1 else 0) → n ≤ D) :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ D := by sorry
