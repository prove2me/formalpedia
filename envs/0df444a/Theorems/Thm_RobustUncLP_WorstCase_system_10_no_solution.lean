-- Prove2me | Theorems.Thm_RobustUncLP_WorstCase_system_10_no_solution
-- name    : RobustUncLP.WorstCase.system_10_no_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:51:55.19951+00:00
-- url     : https://prove2.me/theorems/4da66b80-d9fb-43a7-b0fc-06bcedbf15dc
-- title:
--   (10), §2.2, proof of Proposition 2.1, p. 5 — the finite system A₁x ≥ 0, …, A_Nx ≥ 0, fᵀx = 1 has no solutions
-- statement:
--   Let $\mathcal U$ be a set of real $m\times n$ matrices, $f\in\mathbb R^{n}$, and let $Q\subseteq\mathbb R^{n}$ contain the feasible set $\{x \mid Ax\ge 0,\ f^{T}x = 1\}$ of every instance $A\in\mathcal U$. Let $N \ge 1$ and $A_1,\dots,A_N\in\mathcal U$. If the system
--   $$A_1x \ge 0,\ \dots,\ A_Nx \ge 0,\quad f^{T}x = 1 \tag{10}$$
--   has no solution in $Q$, then it has no solution at all.
--
--   In the proof of Proposition 2.1 this turns the compactness step into a genuinely inconsistent finite linear system, to which Farkas' Lemma applies.
--
--   **Formalization Note** $N \ge 1$ is needed: for $N = 0$, (10) is $f^{T}x = 1$ alone, which may have solutions outside $Q$. The paper takes it for granted. The hypothesis "no solution in $Q$" is stated for the full system (10); the paper derives it from the finite subsystem of rows ("by its origin").
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, p. 5, §2.2, proof of Proposition 2.1, (10) and the sentence after it

import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting
open Matrix

namespace RobustUncLP.WorstCase

theorem system_10_no_solution {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ))
    (f : Fin n → ℝ) (Q : Set (Fin n → ℝ)) (hQ : ∀ A ∈ U, instFeas f A ⊆ Q)
    {N : ℕ} (hN : 0 < N) (A : Fin N → Matrix (Fin m) (Fin n) ℝ) (hA : ∀ p, A p ∈ U)
    (hinQ : ∀ x ∈ Q, ¬ ((∀ p, 0 ≤ A p *ᵥ x) ∧ f ⬝ᵥ x = 1)) :
    ¬ ∃ x : Fin n → ℝ, (∀ p, 0 ≤ A p *ᵥ x) ∧ f ⬝ᵥ x = 1 := by sorry

end RobustUncLP.WorstCase
