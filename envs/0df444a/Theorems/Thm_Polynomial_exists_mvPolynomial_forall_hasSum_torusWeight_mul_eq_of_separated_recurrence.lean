-- Prove2me | Theorems.Thm_Polynomial_exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence
-- name    : Polynomial.exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/e1eed3fd-b320-5f35-a50c-5e259a6cf7d2
-- title:
--   Rationality of a torus-weighted double generating series
-- statement:
--   Let $A:\mathbb{Z}\times\mathbb{Z}\to\mathbb{C}$ be a function, $N_1\in\mathbb{Z}$, let $D_1,D_2\in\mathbb{C}[T]$ satisfy $D_1(0)\neq 0$ and $D_2(0)\neq 0$, and let $M\in\mathbb{N}$. Assume $A$ is supported in the quadrant $n_1,n_2\geq N_1$, i.e. $A(n)=0$ whenever $n_1<N_1$ or $n_2<N_1$, and that $A$ satisfies the separated recurrence
--   $$\sum_{i=0}^{\deg D_1}\sum_{l=0}^{\deg D_2} D_{1,i}\,D_{2,l}\,A(N_1+m_1-i,\;N_1+m_2-l)=0$$
--   for all $m_1,m_2\in\mathbb{N}$ with $m_1\geq M$ or $m_2\geq M$, the sums being over the coefficient indices $0,\dots,\deg D_j$. The conclusion asserts the existence of a single $P\in\mathbb{C}[x_0,x_1,x_2,x_3]$ (a polynomial in four variables, independent of the parameters below) such that for every pair $b_1,b_2\in\mathbb{C}$ there is a radius $r>0$ with the following property for all $X,Y\in\mathbb{C}$ with $\|X\|<r$ and $\|Y\|<r$: the double family
--   $$A(N_1+m_1,N_1+m_2)\,h_{m_1}(b_1,b_2)\,X^{m_1}Y^{m_2},\qquad h_{m}(b_1,b_2)=\sum_{i=0}^{m}b_1^{\,i}b_2^{\,m-i},$$
--   is absolutely summable over $(m_1,m_2)\in\mathbb{N}\times\mathbb{N}$, and its sum $S$ satisfies
--   $$S\cdot D_1(b_1X)\,D_1(b_2X)\,D_2(Y)=P(X,Y,b_1,b_2),$$
--   the evaluation of $P$ at the tuple $(X,Y,b_1,b_2)$.
--
--   This is the rationality statement for a two-variable generating series weighted by the complete homogeneous symmetric functions $h_m(b_1,b_2)$ in an unramified torus (Satake) pair: a coefficient function annihilated by a product recurrence $D_1\otimes D_2$ outside a finite range has its torus-weighted double series equal to a fixed polynomial divided by $D_1(b_1X)D_1(b_2X)D_2(Y)$, with the numerator polynomial in $X,Y,b_1,b_2$ simultaneously — so the resulting identities are polynomial in the Satake parameters. It feeds the cubic-induction arguments on $\mathrm{GL}_3$ Whittaker functions and Rankin–Selberg local integrals, being cited in the treatment of $\iota_{\mathrm{GL}}$-invariant local integrals, of torus shell averages for admissible Whittaker functions, and of the cyclic subspace for $\mathrm{GL}_3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Polynomial.exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_separated_recurrence
    (A : ℤ × ℤ → ℂ) (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ)
    (hD₁ : D₁.eval 0 ≠ 0) (hD₂ : D₂.eval 0 ≠ 0)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0)
    (hrec : ∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
      ∑ i ∈ Finset.range (D₁.natDegree + 1), ∑ l ∈ Finset.range (D₂.natDegree + 1),
        D₁.coeff i * D₂.coeff l * A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0) :
    ∃ P : MvPolynomial (Fin 4) ℂ, ∀ b₁ b₂ : ℂ, ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ =>
        ‖A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) *
          (∑ i ∈ Finset.range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ,
          A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) *
            (∑ i ∈ Finset.range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) * X ^ m.1 * Y ^ m.2) *
        (D₁.eval (b₁ * X) * D₁.eval (b₂ * X) * D₂.eval Y) =
        MvPolynomial.eval (![X, Y, b₁, b₂] : Fin 4 → ℂ) P := by sorry
