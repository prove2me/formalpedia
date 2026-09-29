-- Prove2me | Theorems.Thm_ValuationSubring_exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne
-- name    : ValuationSubring.exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/e9b955b9-1766-53fb-ab4f-0804a8cdb2ae
-- title:
--   Automorphism fixing π and preserving A scales by units
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, with $\mathfrak m_A$ its maximal ideal as a local ring and $A.\mathrm{valuation}$ the associated valuation on $L$ with values in the value group of $A$ (with zero). Let $\pi \in A$ lie in $\mathfrak m_A$ and be nonzero. Assume the archimedean ("rank one") condition: for every nonzero $x \in L$ and every $y \in \mathfrak m_A$ there is a natural number $n$ with $v(y^n) \le v(x)$, where $v = A.\mathrm{valuation}$. Let $\sigma : L \to L$ be a ring automorphism (an isomorphism of additive and multiplicative structures) such that for every $a \in L$ one has $a \in A$ if and only if $\sigma(a) \in A$, and such that $\sigma(\pi) = \pi$ as elements of $L$. The conclusion is that for every nonzero $a \in L$ there exists a unit $u \in A^{\times}$ with $\sigma(a) = u\,a$, the equation holding in $L$ after the evident coercions. Equivalently, $\sigma$ preserves the valuation of every element.
--
--   This is the classical fact that an automorphism of $L$ stabilising a rank-one valuation subring $A$ and fixing one nonzero non-unit of $A$ acts as an isometry for the valuation of $A$. It is used in the analysis of the Galois action on semistable models of curves, where the several `AlgebraicCurve` results on Galois representations and reduction of divisor classes invoke it for the automorphisms of the base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne
    {L : Type*} [Field L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (σ : L ≃+* L) (hA : ∀ a : L, a ∈ A ↔ σ a ∈ A) (hσπ : σ (π : L) = (π : L)) :
    ∀ a : L, a ≠ 0 → ∃ u : Aˣ, σ a = u * a := by sorry
