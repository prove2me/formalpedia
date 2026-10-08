-- Prove2me | Theorems.Thm_SuttonBartoRL_LinearTD_tdA_eq_matrix_form
-- name    : SuttonBartoRL.LinearTD.tdA_eq_matrix_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:47:55.937707+00:00
-- url     : https://prove2.me/theorems/bb0edc57-1049-472c-96be-fdf4b0dd5192
-- title:
--   The $\mathbf A$ matrix of linear TD(0) is $\mathbf X^\top\mathbf D(\mathbf I - \gamma\mathbf P)\mathbf X$
-- statement:
--   Let a finite MDP with dynamics $p(s', r \mid s, a)$, a policy $\pi$, a state weighting $\mu$, a feature matrix $\mathbf X$ (the $|\mathcal S| \times d$ matrix with the feature vectors $\mathbf x(s)$ as its rows) and a discount rate $\gamma$ be given. Let $\mathbf P$ be the $|\mathcal S| \times |\mathcal S|$ matrix of the transition probabilities $p(s' \mid s) = \sum_a \pi(a \mid s) p(s' \mid s, a)$ under $\pi$, and $\mathbf D$ the diagonal matrix with the $\mu(s)$ on its diagonal. Then the matrix $\mathbf A$ of (9.11) satisfies
--
--   $$\mathbf A = \sum_s \mu(s) \sum_a \pi(a \mid s) \sum_{s', r} p(s', r \mid s, a)\, \mathbf x(s)\big(\mathbf x(s) - \gamma \mathbf x(s')\big)^\top = \mathbf X^\top \mathbf D(\mathbf I - \gamma \mathbf P)\mathbf X .$$
--
--   The matrix form reduces the positive definiteness of $\mathbf A$ to that of the inner "key matrix" $\mathbf D(\mathbf I - \gamma \mathbf P)$.
--
--   **Formalization Note** The book states the identity "in the continuing case with $\gamma < 1$", with $\mu$ the stationary distribution under $\pi$; the identity is pure algebra and is stated here for every $\gamma$ and every $\mu$, which is a stronger statement. The book's first line writes $p(r, s' \mid s, a)$ with its arguments in the opposite order to (3.2); it is the same dynamics $p(s', r \mid s, a)$.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, box "Proof of Convergence of Linear TD(0)", p. 206

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

open Matrix

namespace SuttonBartoRL.LinearTD

/-- Sutton & Barto (2018), box "Proof of Convergence of Linear TD(0)", p. 206: the `A` matrix (9.11)
of linear TD(0) can be written `A = XᵀD(I − γP)X`, where `D = diag(µ)`, `P` is the state-transition
matrix of the chain induced by `π`, and `X` has the feature vectors `x(s)` as its rows. -/
theorem tdA_eq_matrix_form {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (X : Matrix S (Fin d) ℝ) (γ : ℝ) :
    tdA M π μ X γ = Xᵀ * diagonal μ * (1 - γ • M.policyTrans π) * X := by sorry

end SuttonBartoRL.LinearTD
