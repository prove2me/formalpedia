-- Prove2me | Theorems.Thm_ProcFlex_DMGI_lemma_1
-- name    : ProcFlex.DMGI.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:18.334025+00:00
-- url     : https://prove2.me/theorems/53b90fbf-cba8-4a4d-9245-00c862e1976a
-- title:
--   Lemma 1: product dual values at a basic feasible solution
-- statement:
--   Consider a basic feasible solution $(y^*,z^*)$ of the dual profit program. For every product $i$, its dual value is its own margin, zero, or the difference between its margin and a strictly smaller product margin:
--
--   $$
--   y_i^*=p_i\quad\text{or}\quad y_i^*=0\quad\text{or}\quad y_i^*=p_i-p_{i'}\text{ for some }p_{i'}<p_i.
--   $$
--
--   The finite menu of possible dual values motivates the DMGI's level assignment.
--
--   **Formalization Note** A basic feasible solution is represented as an extreme point of the dual feasible polyhedron.
-- source:
--   Wang, Wang & Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 22 May 2020), p. 16, Lemma 1

import Mathlib
import Definitions.Def_ProcFlex_DMGI_Model

namespace ProcFlex.DMGI

/-- Lemma 1, p. 16: the permitted product dual values at a basic feasible solution. -/
theorem lemma_1 {m n T : ℕ} (S : System m n T) (hS : S.IsValid)
    (A : Design m n) (y : Fin n → ℝ) (z : Fin m → ℝ)
    (hbasic : (y, z) ∈ Set.extremePoints ℝ
      {q : (Fin n → ℝ) × (Fin m → ℝ) | DualFeasible S A q.1 q.2}) :
    ∀ i, y i = S.p i ∨ y i = 0 ∨
      ∃ i' : Fin n, S.p i' < S.p i ∧ y i = S.p i - S.p i' := by sorry

end ProcFlex.DMGI
