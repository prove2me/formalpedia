-- Prove2me | Theorems.Thm_VanderbeiLP_Simplex_nonterminating_implies_cycling
-- name    : VanderbeiLP.Simplex.nonterminating_implies_cycling
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T16:55:07.124791+00:00
-- url     : https://prove2.me/theorems/84b1dd0d-aaa7-4ea1-947b-e195e551e723
-- title:
--   Theorem 3.1 — a nonterminating simplex run must cycle
-- statement:
--   Consider a standard-form linear program with data $A \in \mathbb{R}^{m\times n}$, $b\in\mathbb{R}^m$, $c \in \mathbb{R}^n$, and an infinite run of the simplex method: a sequence of dictionaries $D_0, D_1, D_2, \dots$ with $D_0$ feasible, in which each $D_{t+1}$ is obtained from $D_t$ by a simplex pivot (an entering candidate $x_k$ with $\bar c_k > 0$ and a leaving candidate chosen by the ratio test, by any rule). Then the run visits some dictionary more than once:
--   $$
--   \exists\, s < t:\quad D_s = D_t .
--   $$
--
--   This is the first step of the chapter's termination analysis: a variant of the simplex method terminates as soon as it is known never to cycle.
--
--   **Formalization Note** Dictionaries are identified with their basic sets, so $D_s = D_t$ means that the same variables are basic.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 27 (PDF 44), Theorem 3.1

import Mathlib
import Definitions.Def_VanderbeiLP_Simplex_Dictionary
import Definitions.Def_VanderbeiLP_Simplex_PivotRules

namespace VanderbeiLP.Simplex

/-- **Vanderbei, Theorem 3.1 (p. 27).** If the simplex method fails to terminate, then it must
cycle: an infinite run of simplex pivots (any choice of entering and leaving candidates at each
step) started at a feasible dictionary visits some dictionary more than once. -/
theorem nonterminating_implies_cycling {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (D : ℕ → Dictionary A) (h0 : (D 0).IsFeasible b)
    (hstep : ∀ t, Dictionary.IsSimplexPivot b c (D t) (D (t + 1))) :
    ∃ s t, s < t ∧ D s = D t := by sorry

end VanderbeiLP.Simplex
