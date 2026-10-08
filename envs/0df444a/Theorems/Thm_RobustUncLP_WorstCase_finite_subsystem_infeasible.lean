-- Prove2me | Theorems.Thm_RobustUncLP_WorstCase_finite_subsystem_infeasible
-- name    : RobustUncLP.WorstCase.finite_subsystem_infeasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T05:51:46.873253+00:00
-- url     : https://prove2.me/theorems/7835901b-87e1-45da-a4e7-96beac7b7960
-- title:
--   §2.2, proof of Proposition 2.1, p. 5 — compactness: a finite subsystem of (8) already has no solution in Q
-- statement:
--   Let $\mathcal U$ be a set of real $m\times n$ matrices, $f \in \mathbb R^{n}$, and let $Q \subseteq \mathbb R^{n}$ be compact. Suppose the system (8) has no solution in $Q$, that is, no $x \in Q$ satisfies $Ax \ge 0$ for all $A\in\mathcal U$ together with $f^{T}x = 1$. Then there are finitely many instances $A_1,\dots,A_N \in \mathcal U$ and row indices $i_1,\dots,i_N \in \{1,\dots,m\}$ such that, writing $a_p$ for the $i_p$-th row of $A_p$, the finite subsystem
--   $$a_p^{T}x \ge 0,\quad p = 1,\dots,N, \qquad f^{T}x = 1$$
--   has no solution $x \in Q$.
--
--   This is the compactness step of the proof of Proposition 2.1: it reduces the semi-infinite system of the robust counterpart to finitely many constraints on $Q$.
--
--   **Formalization Note** The instance $A_p$ "from which $a_p$ comes" is recorded together with the row index $i_p$. $N = 0$ is allowed: then the subsystem is $f^{T}x = 1$ alone. The paper's $N \ge 1$ can be obtained by repeating any instance when $\mathcal U \neq \emptyset$ and $m \ge 1$, so it is not part of the conclusion (with $m = 0$ there are no rows to select).
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, p. 5, §2.2, proof of Proposition 2.1, 'By the standard compactness arguments …'

import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting
open Matrix

namespace RobustUncLP.WorstCase

theorem finite_subsystem_infeasible {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ))
    (f : Fin n → ℝ) (Q : Set (Fin n → ℝ)) (hQ : IsCompact Q)
    (hno : ∀ x ∈ Q, x ∉ robustFeas U f) :
    ∃ (N : ℕ) (A : Fin N → Matrix (Fin m) (Fin n) ℝ) (row : Fin N → Fin m),
      (∀ p, A p ∈ U) ∧ ∀ x ∈ Q, ¬ ((∀ p, 0 ≤ A p (row p) ⬝ᵥ x) ∧ f ⬝ᵥ x = 1) := by sorry

end RobustUncLP.WorstCase
