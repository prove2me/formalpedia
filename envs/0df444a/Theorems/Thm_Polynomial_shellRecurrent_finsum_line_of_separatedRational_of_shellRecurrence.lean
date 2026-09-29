-- Prove2me | Theorems.Thm_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence
-- name    : Polynomial.shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/4a1e17d3-5df0-5444-a8bb-4b0fdbd93437
-- title:
--   Line sums of a separated-rational array satisfy a linear recurrence
-- statement:
--   Let $A:\mathbb{Z}\times\mathbb{Z}\to\mathbb{C}$ and $b:\mathbb{Z}\to\mathbb{C}$ be arbitrary functions, let $\alpha,\beta\in\mathbb{C}$ be non-zero, and let $e_1,e_2$ be strictly positive natural numbers. Assume, first, that there are an integer $N_1$, polynomials $D_1,D_2\in\mathbb{C}[X]$ with $D_1(0)\neq 0$ and $D_2(0)\neq 0$, and a natural number $M$ such that $A(n)=0$ whenever $n_1<N_1$ or $n_2<N_1$, and such that for all naturals $m_1,m_2$ with $M\le m_1$ or $M\le m_2$ one has $\sum_{i\le\deg D_1}\sum_{l\le\deg D_2} D_{1,i}D_{2,l}\,A(N_1+m_1-i,\;N_1+m_2-l)=0$, the indices running over $0,\dots,\deg D_j$ and $D_{j,k}$ denoting coefficients. Assume, second, the corresponding one-variable condition for $b$: there are an integer $N_2$, a polynomial $E$ with $E(0)\neq 0$ and a natural $M'$ with $b(m)=0$ for $m<N_2$ and $\sum_{i\le \deg E}E_i\,b(N_2+m-i)=0$ for all naturals $m\ge M'$. The conclusion is that the line-sum function $t\mapsto \sum^{\mathrm{f}}_{n\in\mathbb{Z}^2}\bigl[e_1n_1+e_2n_2=t\bigr]A(n)\,b(n_1)\,\alpha^{n_1}\beta^{n_2}$, formed as a finite-support sum over $\mathbb{Z}^2$ of the terms cut out by the indicator of the line $e_1n_1+e_2n_2=t$, satisfies the same one-variable condition: there exist an integer $N$, a polynomial $E$ with $E(0)\neq 0$ and a natural $M$ such that this function vanishes at every $m<N$ and such that $\sum_{i\le\deg E}E_i$ times its value at $N+m-i$ vanishes for every natural $m\ge M$.
--
--   This is the closure statement underlying the passage from a separated-rational double array, weighted by a linearly recurrent sequence and by the characters $n_1\mapsto\alpha^{n_1}$, $n_2\mapsto\beta^{n_2}$, to a single one-variable sequence satisfying a linear recurrence with non-vanishing constant term and vanishing far to the left; the hypotheses on $A$ express that $D_1(X)D_2(Y)$ times the associated double generating series is a polynomial outside a finite box, and those on $b$ the analogous one-variable condition. It is used in the rationality argument for the Rankin–Selberg type series, being cited by [`Polynomial.exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence`](thm.html#Polynomial.exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

theorem Polynomial.shellRecurrent_finsum_line_of_separatedRational_of_shellRecurrence
    (A : ℤ × ℤ → ℂ) (b : ℤ → ℂ) (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hA : ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ), D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0))
    (hb : ∃ (N₂ : ℤ) (E : Polynomial ℂ) (M' : ℕ), E.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N₂ → b m = 0) ∧
      (∀ m : ℕ, M' ≤ m →
        ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * b (N₂ + (m : ℤ) - (i : ℤ)) = 0)) :
    (∃ (N : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧ (∀ m : ℤ, m < N → (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
        if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then A n * b n.1 * α ^ n.1 * β ^ n.2 else 0) m = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
        if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then A n * b n.1 * α ^ n.1 * β ^ n.2 else 0) (N + (m : ℤ) - (i : ℤ)) = 0)) := by sorry
