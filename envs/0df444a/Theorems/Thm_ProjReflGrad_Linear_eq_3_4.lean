-- Prove2me | Theorems.Thm_ProjReflGrad_Linear_eq_3_4
-- name    : ProjReflGrad.Linear.eq_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:02.990988+00:00
-- url     : https://prove2.me/theorems/d09740f3-6345-4cf4-b6aa-4ddfcbdf487a
-- title:
--   (3.4), proof of Lemma 3.1, p. 5 — 2λ⟨F(y_{n−1}), y_n − x_{n+1}⟩ ≤ ‖x_{n+1} − x_n‖² − ‖x_n − y_n‖² − ‖x_{n+1} − y_n‖², n ≥ 2
-- statement:
--   Let $H$ be a real Hilbert space, $C\subseteq H$ nonempty, closed and convex, $F:H\to H$, $\lambda\in\mathbb R$, and $(x_n),(y_n)$ a run of Algorithm 3.1. Then for every $n\ge2$
--   $$2\lambda\langle F(y_{n-1}),\,y_n-x_{n+1}\rangle\ \le\ \|x_{n+1}-x_n\|^2-\|x_n-y_n\|^2-\|x_{n+1}-y_n\|^2 .\qquad(3.4)$$
--
--   The estimate follows from the variational characterization of $x_n=P_C(x_{n-1}-\lambda F(y_{n-1}))$ tested at $x_{n+1}$ and $x_{n-1}$, and controls the term $\langle F(y_{n-1}),y_n-x_{n+1}\rangle$ that appears after adding strong monotonicity to (3.2).
--
--   **Formalization Note.** The paper's proof uses $x_{n-1}\in C$; since Algorithm 3.1 allows $x_0\notin C$, this requires $n-1\ge1$, hence the range $n\ge2$. The sign of $\lambda$ plays no role.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 5, (3.4), proof of Lemma 3.1

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

namespace ProjReflGrad.Linear

/-- Inequality (3.4), proof of Lemma 3.1 (Malitsky 2015, p. 5), for `n ≥ 2` (so that
`x_{n-1} ∈ C`): along a run of Algorithm 3.1 with `C` nonempty, closed and convex in a Hilbert space,
`2λ⟨F(y_{n-1}), y_n - x_{n+1}⟩ ≤ ‖x_{n+1} - x_n‖² - ‖x_n - y_n‖² - ‖x_{n+1} - y_n‖²`. -/
theorem eq_3_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (hne : C.Nonempty) (F : H → H) (lam : ℝ)
    (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) :
    ∀ n : ℕ, 2 ≤ n →
      2 * lam * inner ℝ (F (y (n - 1))) (y n - x (n + 1)) ≤
        ‖x (n + 1) - x n‖ ^ 2 - ‖x n - y n‖ ^ 2 - ‖x (n + 1) - y n‖ ^ 2 := by sorry

end ProjReflGrad.Linear
