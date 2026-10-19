-- Prove2me | Theorems.Thm_ParamSDO_Transition_theorem_1
-- name    : ParamSDO.Transition.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:21.061962+00:00
-- url     : https://prove2.me/theorems/601a1dbd-ed4a-4a90-8f43-15c109fbbf6a
-- title:
--   Theorem 1, p. 8 — the set of transition points of the optimal partition of a parametric SDO problem is finite
-- statement:
--   Let $A^1,\dots,A^m,C,\bar C$ be real symmetric $n\times n$ matrices and $b\in\mathbb R^m$, and consider the parametric semidefinite pair
--   $$
--   (\mathrm P_\epsilon)\ \inf_X\{\langle C+\epsilon\bar C,X\rangle:\ \langle A^i,X\rangle=b_i,\ X\succeq0\},\qquad
--   (\mathrm D_\epsilon)\ \sup_{(y,S)}\Big\{b^Ty:\ \sum_i y_iA^i+S=C+\epsilon\bar C,\ S\succeq0\Big\},
--   $$
--   with optimal value $v(\epsilon)$, domain $\mathcal E=\{\epsilon:\ v(\epsilon)>-\infty\}$ and optimal sets $\mathcal P^*(\epsilon)$, $\mathcal D^*(\epsilon)$. Assume the $A^i$ are linearly independent (Assumption 1) and that both problems have positive definite feasible solutions at $\epsilon=0$ (Assumption 2).
--
--   For $\epsilon\in\operatorname{int}(\mathcal E)$ let $\operatorname{rank}X^*(\epsilon)$ and $\operatorname{rank}S^*(\epsilon)$ be the ranks of a maximally complementary optimal solution (a point of the relative interiors of the optimal sets). A point $\bar\epsilon\in\operatorname{int}(\mathcal E)$ is a **transition point** if every neighbourhood of $\bar\epsilon$ in $\operatorname{int}(\mathcal E)$ contains an $\epsilon$ with $\operatorname{rank}X^*(\epsilon)\ne\operatorname{rank}X^*(\bar\epsilon)$ or $\operatorname{rank}S^*(\epsilon)\ne\operatorname{rank}S^*(\bar\epsilon)$ (Definition 5).
--
--   **Theorem 1.** The set of transition points is finite:
--   $$
--   \#\{\bar\epsilon\in\operatorname{int}(\mathcal E):\ \bar\epsilon\ \text{is a transition point}\}<\infty .
--   $$
--
--   Consequently $\operatorname{int}(\mathcal E)$ splits into finitely many invariancy intervals, nonlinearity intervals and transition points, which is the structural basis for computing the nonlinearity intervals of the optimal partition.
--
--   **Formalization Note** The symmetry of the data is the paper's "$C,A^i\in\mathbb S^n$, $\bar C\in\mathbb S^n$"; Assumptions 1–2 are standing for the whole paper (p. 2). $v$ is an `EReal` infimum, ranks are taken at relative-interior points of the optimal sets (Definition 1), and transition points are defined by Definition 5 itself, not through the sets $\mathcal S_{(\theta,\sigma)}$ of the proof.
-- source:
--   Hauenstein, Mohammad-Nezhad, Tang & Terlaky, On computing the nonlinearity interval in parametric semidefinite optimization, arXiv:1908.10499v3, p. 8, Theorem 1 (standing Assumptions 1–2, p. 2; Definition 5, p. 7)

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

namespace ParamSDO.Transition

theorem theorem_1 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    {ϵbar : ℝ | IsTransitionPoint A b C Cbar ϵbar}.Finite := by sorry

end ParamSDO.Transition
