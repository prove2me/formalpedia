-- Prove2me | Theorems.Thm_QAlgorithms_Childs_zsqrtd_isUnit_iff
-- name    : QAlgorithms.Childs.zsqrtd_isUnit_iff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:31:50.529414+00:00
-- url     : https://prove2.me/theorems/c4572864-1091-473a-b976-96a2950169cb
-- title:
--   Units of Z[√d] are exactly the elements of norm ±1
-- statement:
--   Let $d$ be a squarefree integer with $d \ge 2$ (a squarefree positive integer for which $\sqrt d$ is irrational), and let $\mathbb Z[\sqrt d] = \{x + y\sqrt d : x, y \in \mathbb Z\}$ be the ring of integers adjoined with $\sqrt d$. Conjugation is $\overline{x + y\sqrt d} = x - y\sqrt d$, and an element of $\mathbb Z[\sqrt d]$ is a *unit* if its multiplicative inverse (over $\mathbb Q(\sqrt d)$) again lies in $\mathbb Z[\sqrt d]$.
--
--   For all integers $x, y$, the element $\xi = x + y\sqrt d$ is a unit of $\mathbb Z[\sqrt d]$ if and only if
--
--   $$
--   \xi\bar\xi = x^2 - d y^2 = \pm 1.
--   $$
--
--   This identifies the unit group of $\mathbb Z[\sqrt d]$ with the solutions of Pell's equation $x^2 - dy^2 = 1$ and its negative variant $x^2 - dy^2 = -1$; it is the starting point of Hallgren's quantum algorithm, which computes the regulator of the fundamental unit.
--
--   **Formalization Note** $\mathbb Z[\sqrt d]$ is Mathlib's `ℤ√d` (pairs $\langle x, y\rangle$ with the multiplication of $x + y\sqrt d$), and "unit" is `IsUnit`; since $\mathbb Z[\sqrt d]$ embeds in the field $\mathbb Q(\sqrt d)$ for non-square $d$, this agrees with the source's definition. The identity $\xi\bar\xi = x^2 - dy^2$ is definitional, so only $x^2 - dy^2 \in \{1, -1\}$ is stated.
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 43, Proposition 8.1. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_Basic
set_option autoImplicit false

namespace QAlgorithms.Childs

/-- Childs, Proposition 8.1, PDF p. 43. Let `d` be a squarefree integer with `d ≥ 2`. Then
`ξ = x + y√d` is a unit in `Z[√d]` if and only if `ξ ξ̄ = x² − d y² = ±1`. -/
theorem zsqrtd_isUnit_iff (d : ℤ) (hd_sqfree : Squarefree d) (hd : 2 ≤ d) (x y : ℤ) :
    IsUnit (⟨x, y⟩ : ℤ√d) ↔ x ^ 2 - d * y ^ 2 = 1 ∨ x ^ 2 - d * y ^ 2 = -1 := by
  sorry


end QAlgorithms.Childs
