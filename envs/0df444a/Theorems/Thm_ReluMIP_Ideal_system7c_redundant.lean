-- Prove2me | Theorems.Thm_ReluMIP_Ideal_system7c_redundant
-- name    : ReluMIP.Ideal.system7c_redundant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:20.374061+00:00
-- url     : https://prove2.me/theorems/3bb50439-8bfd-4cab-b04c-089cf286b0b8
-- title:
--   App. A.1, pp. 14–15 — the family (7c) is redundant given (7a), (7b), (7d)
-- statement:
--   Let $f(x)=w\cdot x+b$ and $L,U\in\mathbb R^\eta$, with sign-adjusted bounds $\breve L,\breve U$. Every point $(x,y,z)$ of the LP relaxation of formulation (6), that is, every point satisfying (7a), (7b) and (7d), also satisfies every inequality of the family (7c):
--   $$
--   y\ge\sum_{i\in I}w_i\bigl(x_i-\breve U_i(1-z)\bigr)+\Bigl(b+\sum_{i\notin I}w_i\breve L_i\Bigr)z\qquad\text{for all }I\subseteq\operatorname{supp}(w).
--   $$
--
--   Together with the Fourier–Motzkin step, this shows that the projection of the multiple choice formulation (5) is exactly the LP relaxation of (6).
--
--   **Formalization Note** No hypothesis on $L,U$ or strict activity is needed, so none is assumed. The inequality (7c) is stated in the general-sign form explained in the Fourier–Motzkin milestone.
-- source:
--   arXiv:1811.08359v2, App. A.1, pp. 14–15 (the paragraph after display (7))

import Mathlib
import Definitions.Def_ReluMIP_Ideal_Setting

namespace ReluMIP.Ideal

/-- App. A.1, pp. 14–15 (arXiv:1811.08359v2): the family (7c) is redundant — every point of the
LP relaxation of (6) (that is, of (7a), (7b), (7d)) satisfies every inequality of (7c). -/
theorem system7c_redundant {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) :
    ∀ p ∈ relax6 w b L U, ∀ I : Finset (Fin η), I ⊆ supp w →
      rhs7c w b L U I p.1 p.2.2 ≤ p.2.1 := by sorry

end ReluMIP.Ideal
