-- Prove2me | Theorems.Thm_Polynomial_exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line
-- name    : Polynomial.exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/dae69082-165a-5210-9424-c0ae40182960
-- title:
--   Recurrent line sums make a double Laurent series rational
-- statement:
--   Let $w\colon\mathbb Z\times\mathbb Z\to\mathbb C$ be a function and $N_1\in\mathbb Z$ be such that $w(n)=0$ whenever $n_1<N_1$ or $n_2<N_1$, and let $e_1,e_2$ be positive natural numbers; write $\ell(n)=e_1n_1+e_2n_2$ and let $c\colon\mathbb Z\to\mathbb C$ be the line-sum function $c(t)=\sum^{\mathrm f}_{n\in\mathbb Z^2}\,[\ell(n)=t]\,w(n)$, the finite sum (`finsum`) of the function equal to $w(n)$ on the fibre $\ell^{-1}(t)$ and to $0$ elsewhere. Assume that $c$ is recurrent in the following sense: there are $N\in\mathbb Z$, a polynomial $E\in\mathbb C[X]$ with $E(0)\neq 0$, and $M\in\mathbb N$ such that $c(m)=0$ for every integer $m<N$, and $\sum_{i=0}^{\deg E}E_i\,c(N+m-i)=0$ for every natural number $m\geq M$ (the sum being taken over $i$ in `Finset.range (E.natDegree + 1)`, with $E_i$ the $i$-th coefficient of $E$). Then there exist polynomials $P,Q\in\mathbb C[X]$ and an integer $m_0$ with $Q\neq 0$ such that for every $X\in\mathbb C$ with $X\neq 0$ for which the family $n\mapsto w(n)X^{\ell(n)}$ is summable over $\mathbb Z\times\mathbb Z$, one has $\bigl(\sum_{n\in\mathbb Z^2}w(n)X^{\ell(n)}\bigr)\,Q(X)=X^{m_0}P(X)$. Summability at $X$ is a hypothesis, not an assertion: nothing is claimed at points where the double family fails to be summable.
--
--   This is the analytic form of the classical equivalence between linear recurrences for the coefficients of a series and rationality of its sum, here for a doubly indexed Laurent family whose coefficients are regrouped along the fibres of the linear form $e_1n_1+e_2n_2$. It is used in the Rankin–Selberg input to the Langlands–Tunnell step and in the companion statement [`Polynomial.exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence`](thm.html#Polynomial.exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence), where local zeta-type sums are identified with rational functions of the uniformiser.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

theorem Polynomial.exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line
    (w : ℤ × ℤ → ℂ) (N₁ : ℤ) (hw : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → w n = 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hc : (∃ (N : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧ (∀ m : ℤ, m < N → (fun t : ℤ => ∑ᶠ n : ℤ × ℤ, if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then w n else 0) m = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1), E.coeff i * (fun t : ℤ => ∑ᶠ n : ℤ × ℤ, if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then w n else 0) (N + (m : ℤ) - (i : ℤ)) = 0))) :
    ∃ (P Q : Polynomial ℂ) (m₀ : ℤ), Q ≠ 0 ∧
      ∀ X : ℂ, X ≠ 0 →
        Summable (fun n : ℤ × ℤ => w n * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) →
        (∑' n : ℤ × ℤ, w n * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) * Q.eval X = X ^ m₀ * P.eval X := by sorry
