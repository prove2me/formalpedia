-- Prove2me | Theorems.Thm_ProjReflGrad_Linear_eq_3_2
-- name    : ProjReflGrad.Linear.eq_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:40.534696+00:00
-- url     : https://prove2.me/theorems/0b27aba5-7a5e-4373-afd1-417d86850f2b
-- title:
--   (3.2), proof of Lemma 3.1, p. 4 — the projection inequality along a run
-- statement:
--   Let $H$ be a real Hilbert space, $C\subseteq H$ closed and convex, $F:H\to H$, $\lambda\in\mathbb R$, and $(x_n),(y_n)$ a run of Algorithm 3.1. For every $z\in C$ and every $n\ge0$,
--   $$\|x_{n+1}-z\|^2\ \le\ \|x_n-\lambda F(y_n)-z\|^2-\|x_n-\lambda F(y_n)-x_{n+1}\|^2\ =\ \|x_n-z\|^2-\|x_{n+1}-x_n\|^2-2\lambda\langle F(y_n),x_{n+1}-z\rangle .\qquad(3.2)$$
--
--   The inequality is Lemma 2.1 (ii) for $x_{n+1}=P_C(x_n-\lambda F(y_n))$; the equality is an expansion of squares. It is the starting point of both convergence proofs of the paper.
--
--   **Formalization Note.** The paper uses (3.2) for $z\in S$; it holds for every $z\in C$, which also guarantees $C\neq\emptyset$, so the projection is the true metric projection. The sign of $\lambda$ plays no role.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 4, (3.2), proof of Lemma 3.1

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

namespace ProjReflGrad.Linear

/-- Inequality (3.2), proof of Lemma 3.1 (Malitsky 2015, p. 4): along a run of Algorithm 3.1 with
`C` closed and convex in a Hilbert space, for every `z ∈ C` and every `n`,
`‖x_{n+1} - z‖² ≤ ‖x_n - λF(y_n) - z‖² - ‖x_n - λF(y_n) - x_{n+1}‖²
  = ‖x_n - z‖² - ‖x_{n+1} - x_n‖² - 2λ⟨F(y_n), x_{n+1} - z⟩`. -/
theorem eq_3_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (lam : ℝ)
    (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) (z : H) (hz : z ∈ C) :
    ∀ n : ℕ,
      ‖x (n + 1) - z‖ ^ 2 ≤
          ‖x n - lam • F (y n) - z‖ ^ 2 - ‖x n - lam • F (y n) - x (n + 1)‖ ^ 2 ∧
        ‖x n - lam • F (y n) - z‖ ^ 2 - ‖x n - lam • F (y n) - x (n + 1)‖ ^ 2 =
          ‖x n - z‖ ^ 2 - ‖x (n + 1) - x n‖ ^ 2 - 2 * lam * inner ℝ (F (y n)) (x (n + 1) - z) := by sorry

end ProjReflGrad.Linear
