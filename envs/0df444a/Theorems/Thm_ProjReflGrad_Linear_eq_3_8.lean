-- Prove2me | Theorems.Thm_ProjReflGrad_Linear_eq_3_8
-- name    : ProjReflGrad.Linear.eq_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:29.218468+00:00
-- url     : https://prove2.me/theorems/4c4af30e-37b7-4715-9e94-dbcce105813f
-- title:
--   (3.8), p. 7 — 2λ(⟨F(y_n) − F(z), y_n − z⟩ − m₁(2‖x_n − z‖² − ‖x_{n−1} − z‖²)) ≥ 2λ(⟨F(y_n) − F(z), y_n − z⟩ − m‖y_n − z‖²) ≥ 0
-- statement:
--   Let $(x_n),(y_n)$ be a run of Algorithm 3.1 in a real inner product space $H$ with step $\lambda>0$, and let $F$ be strongly monotone with modulus $m>0$. Let $z\in H$. Then for every $m_1\in(0,m]$ and every $n\ge1$,
--   $$2\lambda\Big(\langle F(y_n)-F(z),y_n-z\rangle-m_1\big(2\|x_n-z\|^2-\|x_{n-1}-z\|^2\big)\Big)\ \ge\ 2\lambda\Big(\langle F(y_n)-F(z),y_n-z\rangle-m\|y_n-z\|^2\Big)\ \ge\ 0 .\qquad(3.8)$$
--
--   The free parameter $m_1$ is what later lets the recursion (3.9) be read as inequality (2.1) of Lemma 2.8 for a whole interval of values $\alpha=2\lambda m_1$.
--
--   **Formalization Note.** The paper applies (3.8) with $z$ the solution; the inequality holds for every $z\in H$, and that is how it is stated. The range is $n\ge1$ because $x_{n-1}$ and the reflection $y_n=2x_n-x_{n-1}$ enter.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 7, (3.8)

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

namespace ProjReflGrad.Linear

/-- Inequality (3.8) (Malitsky 2015, p. 7): along a run of Algorithm 3.1, with `F` strongly
monotone with modulus `m > 0` and `λ > 0`, for every `z`, every `m₁ ∈ (0, m]` and every `n ≥ 1`,
`2λ(⟨F(y_n) - F(z), y_n - z⟩ - m₁(2‖x_n - z‖² - ‖x_{n-1} - z‖²))
  ≥ 2λ(⟨F(y_n) - F(z), y_n - z⟩ - m‖y_n - z‖²) ≥ 0`. -/
theorem eq_3_8 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (F : H → H) (m lam : ℝ) (hm : 0 < m) (hC2s : IsStronglyMonotoneMap F m)
    (hlam0 : 0 < lam) (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) (z : H) :
    ∀ m1 : ℝ, 0 < m1 → m1 ≤ m → ∀ n : ℕ, 1 ≤ n →
      2 * lam * (inner ℝ (F (y n) - F z) (y n - z) - m * ‖y n - z‖ ^ 2) ≤
        2 * lam * (inner ℝ (F (y n) - F z) (y n - z)
          - m1 * (2 * ‖x n - z‖ ^ 2 - ‖x (n - 1) - z‖ ^ 2)) ∧
      0 ≤ 2 * lam * (inner ℝ (F (y n) - F z) (y n - z) - m * ‖y n - z‖ ^ 2) := by sorry

end ProjReflGrad.Linear
