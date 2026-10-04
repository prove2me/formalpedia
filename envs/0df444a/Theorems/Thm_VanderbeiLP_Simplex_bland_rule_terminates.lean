-- Prove2me | Theorems.Thm_VanderbeiLP_Simplex_bland_rule_terminates
-- name    : VanderbeiLP.Simplex.bland_rule_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T17:03:40.192574+00:00
-- url     : https://prove2.me/theorems/b18400d9-0f36-4a8e-8b07-c55d8a5406ad
-- title:
--   Theorem 3.3 — the simplex method terminates under Bland's rule
-- statement:
--   Consider a standard-form linear program with data $A \in \mathbb{R}^{m\times n}$, $b\in\mathbb{R}^m$, $c \in \mathbb{R}^n$, and a feasible dictionary $D_0$. Run the simplex method from $D_0$ choosing both the entering and the leaving variable by **Bland's rule**: among the candidates, the variable $x_k$ with the smallest index $k$ (indices $1,\dots,n$ for the decision variables and $n+1,\dots,n+m$ for the slacks). Then the simplex method always terminates:
--
--   1. there is no infinite sequence $D_0 \to D_1 \to D_2 \to \cdots$ of Bland pivots;
--   2. there are $T \ge 0$ and Bland pivots $D_0 \to D_1 \to \dots \to D_T$ such that the method stops at $D_T$: either
--   $$
--   \bar c_j \le 0 \text{ for every nonbasic } j \qquad\text{or}\qquad \bar a_{ik} \le 0 \text{ for every basic } i,
--   $$
--   where $x_k$ is the entering variable chosen by Bland's rule in $D_T$ — that is, $D_T$ is optimal, or it shows that the problem is unbounded.
--
--   Together with Phase I, this gives a variant of the simplex method that is guaranteed to finish, the basis of the fundamental theorem of linear programming.
--
--   **Formalization Note** The book's statement is the termination claim; part 2 records what termination means for the method as defined on pp. 15–19 (it stops only when there is no entering candidate or no positive $\bar a_{ik}$ in the entering column), so the statement cannot hold merely because pivots fail to exist. Bland's rule compares the indices of `Fin (n + m)`, decision variables before slacks.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 31 (PDF 48), Theorem 3.3, with Bland's rule as defined at the start of §3.4 on the same page

import Mathlib
import Definitions.Def_VanderbeiLP_Simplex_Dictionary
import Definitions.Def_VanderbeiLP_Simplex_PivotRules

namespace VanderbeiLP.Simplex

/-- **Vanderbei, Theorem 3.3 (p. 31).** The simplex method always terminates provided that both
the entering and the leaving variable are chosen according to Bland's rule. Started at any
feasible dictionary `D₀`:
1. there is no infinite sequence of Bland pivots starting at `D₀`;
2. a finite sequence of Bland pivots leads from `D₀` to a dictionary at which the method stops,
   either optimal (no `c̄_j > 0`) or exhibiting unboundedness (the Bland entering column has
   no `ā_{ik} > 0`). -/
theorem bland_rule_terminates {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (D₀ : Dictionary A) (h0 : D₀.IsFeasible b) :
    (¬ ∃ D : ℕ → Dictionary A, D 0 = D₀ ∧
      ∀ t, Dictionary.IsBlandPivot b c (D t) (D (t + 1))) ∧
    ∃ (T : ℕ) (D : ℕ → Dictionary A), D 0 = D₀ ∧
      (∀ t < T, Dictionary.IsBlandPivot b c (D t) (D (t + 1))) ∧
      (D T).IsBlandTerminal c := by sorry

end VanderbeiLP.Simplex
