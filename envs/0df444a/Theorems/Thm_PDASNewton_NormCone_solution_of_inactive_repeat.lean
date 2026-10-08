-- Prove2me | Theorems.Thm_PDASNewton_NormCone_solution_of_inactive_repeat
-- name    : PDASNewton.NormCone.solution_of_inactive_repeat
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:20.117389+00:00
-- url     : https://prove2.me/theorems/c58c6943-8af1-42b5-8dd0-6a3a3308aebf
-- title:
--   Proof of Theorem 3.3, p. 9 — if 𝓘_k = 𝓘_{k+1} then (yᵏ⁺¹, λᵏ⁺¹) solves (3.1)
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$, $f, \psi \in \mathbb{R}^n$, $c \in \mathbb{R}$, and let $(y^k, \lambda^k)_{k\ge0}$ be a run of the primal-dual active set algorithm, with active sets $\mathcal{A}_k = \{i : \lambda^k_i + c(y^k_i - \psi_i) > 0\}$ and inactive sets $\mathcal{I}_k$ their complements. If for some $k$ the active (equivalently, inactive) sets of two consecutive iterates coincide, $\mathcal{I}_k = \mathcal{I}_{k+1}$, then $(y^{k+1}, \lambda^{k+1})$ solves (3.1):
--   $$Ay^{k+1} + \lambda^{k+1} = f, \qquad \lambda^{k+1} - \max\big(0, \lambda^{k+1} + c(y^{k+1} - \psi)\big) = 0.$$
--
--   This is the termination criterion of the algorithm: once the active set repeats, the current iterate is the solution. In the proof of Theorem 3.3 it combines with the monotone merit function to give convergence in finitely many steps.
--
--   **Formalization Note** The statement holds for every matrix and every $c$; no matrix hypothesis and no sign of $c$ is used. The preceding sentence of the page (existence of an index $\bar k$ with $\mathcal{I}_{\bar k} = \mathcal{I}_{\bar k + 1}$) is not part of this item.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 9, proof of Theorem 3.3, last paragraph

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting
import Definitions.Def_PDASNewton_NormCone_Setting

open Filter Topology Matrix

namespace PDASNewton.NormCone

theorem solution_of_inactive_repeat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (f ψ : Fin n → ℝ) (c : ℝ) (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, PDASNewton.Local.activeSet c ψ (y k) (lam k) = PDASNewton.Local.activeSet c ψ (y (k + 1)) (lam (k + 1)) →
      PDASNewton.Local.IsSolution A f ψ c (y (k + 1)) (lam (k + 1)) := by sorry

end PDASNewton.NormCone
