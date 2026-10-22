-- Prove2me | Theorems.Thm_PermPartialTranspose_CommonSolutions_theorem_1
-- name    : PermPartialTranspose.CommonSolutions.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:37.870359+00:00
-- url     : https://prove2.me/theorems/269e2773-fd1d-4c0c-b0ad-dce3bd4d5346
-- title:
--   Theorem 1 (corrected): common braid and Yang–Baxter solutions
-- statement:
--   Let $d\ge2$, let $a\ne0$, and set $\check R(u)=a\mathbf1+uP+bP_*$ on $\mathbb C^d\otimes\mathbb C^d$, where $P$ exchanges the factors and $P_*=\Theta_2(P)$. With $a,b$ fixed and $u$ varying as the coefficient of $P$, the corrected classification has three parts:
--
--   1. For each $u\ne0$, $\check R(u)$ satisfies the braid relation exactly when $d=2$ and either $a=-b$ or $a=b=-u$.
--   2. If $b\ne0$, the family satisfies the additive Yang–Baxter equation (15) for all parameters exactly when $d=2$ and $a=-b$.
--   3. The family satisfies the multiplicative Yang–Baxter equation (14) for all parameters exactly when $d=2$ and $a=-b$.
--
--   The result identifies the common braid and spectral-parameter solutions of the paper's three-generator family.
--
--   **Formalization Note** The restrictions $d\ge2$, $u\ne0$ in the braid clause, and $b\ne0$ in the additive clause correct degenerate counterexamples to the printed wording. At $d=1$ all operators are scalar; at $u=0$ the paper's $\mathbf1+vP_*$ solves the braid relation in higher dimension; at $b=0$ the rational family $a\mathbf1+uP$ solves (15) in every dimension. Equation (14) is quantified over all complex $x,y$, equivalent to the paper's nonzero exponential parameters by polynomial identity.
-- source:
--   Zhang, Kauffman & Werner, Permutation and Its Partial Transpose, arXiv:quant-ph/0606005v1, p. 22, Theorem 1 (corrected); pp. 20–21, (60); p. 9, (21)

import Mathlib
import Definitions.Def_PermPartialTranspose_CommonSolutions_Ops

namespace PermPartialTranspose.CommonSolutions

/-- Theorem 1, p. 22, corrected at u = 0, b = 0, and d = 1. -/
theorem theorem_1 (d : ℕ) (hd : 2 ≤ d) (a b : ℂ) (ha : a ≠ 0) :
    (∀ u : ℂ, u ≠ 0 →
      (BraidRel (Rcheck d a u b) ↔
        d = 2 ∧ (a = -b ∨ (a = b ∧ b = -u)))) ∧
    (b ≠ 0 → (AdditiveYBE d a b ↔ d = 2 ∧ a = -b)) ∧
    (MultiplicativeYBE d a b ↔ d = 2 ∧ a = -b) := by sorry

end PermPartialTranspose.CommonSolutions
