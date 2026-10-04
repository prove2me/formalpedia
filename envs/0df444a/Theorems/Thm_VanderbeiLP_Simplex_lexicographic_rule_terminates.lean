-- Prove2me | Theorems.Thm_VanderbeiLP_Simplex_lexicographic_rule_terminates
-- name    : VanderbeiLP.Simplex.lexicographic_rule_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T17:01:03.81053+00:00
-- url     : https://prove2.me/theorems/5c5fe0c4-8428-4fef-a054-627a5071f988
-- title:
--   Theorem 3.2 — the simplex method terminates under the lexicographic rule
-- statement:
--   Consider a standard-form linear program with data $A \in \mathbb{R}^{m\times n}$, $b\in\mathbb{R}^m$, $c \in \mathbb{R}^n$, and a feasible dictionary $D_0$. Run the simplex method from $D_0$ with any entering candidate at each step and the leaving variable selected by the **lexicographic rule**: the right-hand sides of $D_0$ are perturbed by symbols $0 < \epsilon_m \ll \dots \ll \epsilon_1 \ll$ all data, and the leaving variable minimizes the perturbed ratio. Then the method terminates: there is no infinite sequence
--   $$
--   D_0 \to D_1 \to D_2 \to \cdots
--   $$
--   of such pivots.
--
--   The lexicographic rule is the first of the two anticycling rules of the chapter; it fixes the leaving variable and leaves the entering variable free.
--
--   **Formalization Note** The symbolic perturbation is encoded by the coefficient vectors $(\bar b_i, r_{i1},\dots,r_{im})$ compared lexicographically (see the definition `PivotRules`); no real value of $\epsilon$ is fixed. The $p$-th symbol is attached in $D_0$ to the row of its $p$-th basic variable in increasing index order.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 30 (PDF 47), Theorem 3.2, with the lexicographic method of pp. 28–30 (PDF 45–47)

import Mathlib
import Definitions.Def_VanderbeiLP_Simplex_Dictionary
import Definitions.Def_VanderbeiLP_Simplex_PivotRules

namespace VanderbeiLP.Simplex

/-- **Vanderbei, Theorem 3.2 (p. 30).** The simplex method always terminates provided that the
leaving variable is selected by the lexicographic rule: started at any feasible dictionary
`D₀`, there is no infinite sequence of pivots in which each entering variable is an entering
candidate and each leaving variable is chosen by the lexicographic rule of the run started
at `D₀`. -/
theorem lexicographic_rule_terminates {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (D₀ : Dictionary A) (h0 : D₀.IsFeasible b) :
    ¬ ∃ D : ℕ → Dictionary A, D 0 = D₀ ∧
      ∀ t, Dictionary.IsLexPivot D₀ b c (D t) (D (t + 1)) := by sorry

end VanderbeiLP.Simplex
