-- Prove2me | Theorems.Thm_ParamSDO_Transition_optimality_conditions_1
-- name    : ParamSDO.Transition.optimality_conditions_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:12.111851+00:00
-- url     : https://prove2.me/theorems/2223fdee-2431-4c1f-9d28-3ae3beba5c74
-- title:
--   (1), p. 2 — optimality conditions: on int(𝓔), (X, y, S) is optimal iff it is feasible and XS = 0
-- statement:
--   In the setting of the parametric semidefinite pair $(\mathrm P_\epsilon)/(\mathrm D_\epsilon)$ with symmetric data, under Assumptions 1 and 2, fix $\epsilon\in\operatorname{int}(\mathcal E)$. For every $X\in\mathbb R^{n\times n}$, $y\in\mathbb R^m$ and $S\in\mathbb R^{n\times n}$,
--   $$
--   X\in\mathcal P^*(\epsilon)\ \text{and}\ (y,S)\in\mathcal D^*(\epsilon)
--   \iff
--   \begin{cases}\langle A^i,X\rangle=b_i,\ i=1,\dots,m,\\ \sum_{i=1}^m y_iA^i+S=C+\epsilon\bar C,\\ XS=0,\\ X,S\succeq0.\end{cases}
--   \tag{1}
--   $$
--
--   The system (1) is polynomial in $(X,y,S)$, which is what makes the optimal sets semi-algebraic in the proof of Theorem 1.
--
--   **Formalization Note** The right-hand side is written as $X\in\mathcal P$, $(y,S)\in\mathcal D(\epsilon)$, $XS=0$. The symmetry of the data and Assumptions 1–2 are carried as hypotheses.
-- source:
--   Hauenstein, Mohammad-Nezhad, Tang & Terlaky, On computing the nonlinearity interval in parametric semidefinite optimization, arXiv:1908.10499v3, p. 2, display (1)

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

namespace ParamSDO.Transition

theorem optimality_conditions_1 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    ∀ ϵ ∈ interior (domE A b C Cbar), ∀ (X : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ)
      (S : Matrix (Fin n) (Fin n) ℝ),
      (X ∈ Pstar A b C Cbar ϵ ∧ (y, S) ∈ Dstar A b C Cbar ϵ) ↔
        (X ∈ Pfeas A b ∧ (y, S) ∈ Dfeas A C Cbar ϵ ∧ X * S = 0) := by sorry

end ParamSDO.Transition
