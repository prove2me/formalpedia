-- Prove2me | Theorems.Thm_ProjReflGrad_Linear_eq_3_5
-- name    : ProjReflGrad.Linear.eq_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:46.70724+00:00
-- url     : https://prove2.me/theorems/bff03238-19e8-4606-a5aa-f87122b5285a
-- title:
--   (3.5), proof of Lemma 3.1, p. 5 — the Lipschitz estimate of 2λ⟨F(y_n) − F(y_{n−1}), y_n − x_{n+1}⟩
-- statement:
--   Let $H$ be a real inner product space, $F:H\to H$ $L$-Lipschitz with $L>0$, $\lambda>0$, and $(x_n),(y_n)$ a run of Algorithm 3.1. Then for every $n\ge1$
--   $$2\lambda\langle F(y_n)-F(y_{n-1}),\,y_n-x_{n+1}\rangle\ \le\ \lambda L(1+\sqrt2)\|y_n-x_n\|^2+\lambda L\|x_n-y_{n-1}\|^2+\sqrt2\,\lambda L\|x_{n+1}-y_n\|^2 .\qquad(3.5)$$
--
--   This is the only place where the Lipschitz constant enters; the constants $1+\sqrt2$ and $\sqrt2$ are what fix the admissible step range $\lambda<(\sqrt2-1)/L$ of Algorithm 3.1.
--
--   **Formalization Note.** No projection property is used, so $C$ is unrestricted. The page's display ends with a stray closing parenthesis, which is a typo.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 5, (3.5), proof of Lemma 3.1

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

namespace ProjReflGrad.Linear

/-- Inequality (3.5), proof of Lemma 3.1 (Malitsky 2015, p. 5): along a run of Algorithm 3.1 with
`F` `L`-Lipschitz (`L > 0`) and `λ > 0`, for every `n ≥ 1`,
`2λ⟨F(y_n) - F(y_{n-1}), y_n - x_{n+1}⟩
  ≤ λL(1 + √2)‖y_n - x_n‖² + λL‖x_n - y_{n-1}‖² + √2λL‖x_{n+1} - y_n‖²`. -/
theorem eq_3_5 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (F : H → H) (L lam : ℝ) (hL : 0 < L) (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L) (hlam0 : 0 < lam)
    (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) :
    ∀ n : ℕ, 1 ≤ n →
      2 * lam * inner ℝ (F (y n) - F (y (n - 1))) (y n - x (n + 1)) ≤
        lam * L * (1 + Real.sqrt 2) * ‖y n - x n‖ ^ 2 + lam * L * ‖x n - y (n - 1)‖ ^ 2
          + Real.sqrt 2 * lam * L * ‖x (n + 1) - y n‖ ^ 2 := by sorry

end ProjReflGrad.Linear
