-- Prove2me | Theorems.Thm_Polynomial_exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence
-- name    : Polynomial.exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/818d850e-6c5c-5e33-b986-35998808669c
-- title:
--   Rationality of torus sums of separated-recurrent double arrays
-- statement:
--   Let $A:\mathbb Z\times\mathbb Z\to\mathbb C$ and $b:\mathbb Z\to\mathbb C$, let $\alpha,\beta\in\mathbb C$ be non-zero, and let $e_1,e_2$ be positive natural numbers. Assume, first, that there exist $N_1\in\mathbb Z$, polynomials $D_1,D_2\in\mathbb C[T]$ with $D_1(0)\neq 0$ and $D_2(0)\neq 0$, and $M\in\mathbb N$ such that $A(n)=0$ whenever $n_1<N_1$ or $n_2<N_1$, and such that for all $m_1,m_2\in\mathbb N$ with $m_1\ge M$ or $m_2\ge M$ one has $\sum_{i=0}^{\deg D_1}\sum_{l=0}^{\deg D_2} D_{1,i}D_{2,l}\,A(N_1+m_1-i,\;N_1+m_2-l)=0$; second, that there exist $N_2\in\mathbb Z$, a polynomial $E$ with $E(0)\neq0$, and $M'\in\mathbb N$ such that $b(m)=0$ for $m<N_2$ and $\sum_{i=0}^{\deg E}E_i\,b(N_2+m-i)=0$ for all natural $m\ge M'$. Then there exist polynomials $P,Q\in\mathbb C[T]$ with $Q\neq0$ and an integer $m_0$ such that for every non-zero $X\in\mathbb C$ for which the family $n\mapsto A(n)\,b(n_1)\,\alpha^{n_1}\beta^{n_2}X^{e_1n_1+e_2n_2}$ (integer powers) is summable over $\mathbb Z\times\mathbb Z$, $$\Bigl(\sum_{n\in\mathbb Z\times\mathbb Z}A(n)\,b(n_1)\,\alpha^{n_1}\beta^{n_2}X^{e_1n_1+e_2n_2}\Bigr)\cdot Q(X)=X^{m_0}P(X).$$ The polynomials $P,Q$ and the integer $m_0$ are uniform in $X$, while the identity is asserted only at those non-zero $X$ where summability holds.
--
--   This is the rationality statement for the generating series of a double array whose two-variable series has separated denominators, twisted by a linearly recurrent sequence in the first variable and by a character $(\alpha,\beta)$ of the torus, and summed along the integral weights $e_1n_1+e_2n_2$. It is used in the construction of local Rankin–Selberg integrals, where it supplies the rationality in $X$ of such an integral up to a monomial factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Polynomial.exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence
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
    ∃ (P Q : Polynomial ℂ) (m₀ : ℤ), Q ≠ 0 ∧
      ∀ X : ℂ, X ≠ 0 →
        Summable (fun n : ℤ × ℤ =>
          A n * b n.1 * α ^ n.1 * β ^ n.2 * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) →
        (∑' n : ℤ × ℤ, A n * b n.1 * α ^ n.1 * β ^ n.2 * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) * Q.eval X =
          X ^ m₀ * P.eval X := by sorry
