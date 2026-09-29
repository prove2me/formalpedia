-- Prove2me | Theorems.Thm_Polynomial_eq_of_forall_abs_resultant_X_pow_add_C_le
-- name    : Polynomial.eq_of_forall_abs_resultant_X_pow_add_C_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/511e04f5-5683-5bf6-854a-8bef031484e0
-- title:
--   Monic rational polynomials determined by resultant inequalities
-- statement:
--   Let $P$ and $Q$ be polynomials in $\mathbb{Q}[X]$, both monic, with $\deg P = \deg Q$ (equality of their `natDegree`s). Let $S$ be a set of integers that is unbounded above and unbounded below, in the sense that for every integer $b$ there is some $c \in S$ with $b \le c$ and also some $c \in S$ with $c \le b$. Assume that for every natural number $n > 0$ and every $c \in S$, whenever the resultant of $X^n + c$ with $P$, computed in $\mathbb{Q}[X]$ after mapping $c$ into $\mathbb{Q}$, is nonzero, one has
--   $$|\mathrm{Res}(X^n + c,\,Q)| \le |\mathrm{Res}(X^n + c,\,P)|.$$
--   Then $P = Q$. Note that only an inequality in one direction is assumed, and only at those pairs $(n,c)$ where the resultant with $P$ does not vanish; no hypothesis is imposed at the remaining pairs.
--
--   An elementary rigidity statement: the sizes of the resultants against the family $X^n + c$ pin down a monic rational polynomial among monic polynomials of the same degree, the comparison at large positive and large negative $c$ forcing equality of all power sums of the roots and hence, by Newton's identities in characteristic zero, equality of the polynomials. It is used in the study of Picard groups of curves, where it converts a numerical estimate for orders of kernels of endomorphisms into the identification of two characteristic polynomials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_eq_of_forall_abs_resultant_X_pow_add_C_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Polynomial.eq_of_forall_abs_resultant_X_pow_add_C_le (P Q : Polynomial ℚ)
    (hP : P.Monic) (hQ : Q.Monic) (hdeg : P.natDegree = Q.natDegree)
    (S : Set ℤ) (hS₁ : ∀ b : ℤ, ∃ c ∈ S, b ≤ c) (hS₂ : ∀ b : ℤ, ∃ c ∈ S, c ≤ b)
    (h : ∀ n : ℕ, 0 < n → ∀ c ∈ S,
      (Polynomial.X ^ n + Polynomial.C (c : ℚ) : Polynomial ℚ).resultant P ≠ 0 →
        |(Polynomial.X ^ n + Polynomial.C (c : ℚ) : Polynomial ℚ).resultant Q| ≤
          |(Polynomial.X ^ n + Polynomial.C (c : ℚ) : Polynomial ℚ).resultant P|) :
    P = Q := by sorry
