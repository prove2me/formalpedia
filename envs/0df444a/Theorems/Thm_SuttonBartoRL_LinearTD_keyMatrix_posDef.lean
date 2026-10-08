-- Prove2me | Theorems.Thm_SuttonBartoRL_LinearTD_keyMatrix_posDef
-- name    : SuttonBartoRL.LinearTD.keyMatrix_posDef
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:48:11.514149+00:00
-- url     : https://prove2.me/theorems/1bfd4a8b-5f1f-4115-8aa1-062a0387417e
-- title:
--   The key matrix $\mathbf D(\mathbf I-\gamma\mathbf P)$ and the $\mathbf A$ matrix of on-policy linear TD(0) are positive definite
-- statement:
--   Let a finite MDP with dynamics $p(s', r \mid s, a)$ and a policy $\pi$ be given, with discount rate $0 \le \gamma < 1$. Let $\mathbf P$ be the transition matrix of the chain induced by $\pi$ and $\mu$ a stationary distribution of it ($\mu \ge 0$, $\sum_s \mu(s) = 1$, $\mu^\top \mathbf P = \mu^\top$) with $\mu(s) > 0$ for every state, and $\mathbf D = \mathrm{diag}(\mu)$. Let $\mathbf X$ be an $|\mathcal S| \times d$ feature matrix with linearly independent columns and $\mathbf A$ the matrix (9.11). Then both the key matrix and $\mathbf A$ are positive definite:
--
--   $$y^\top \mathbf D(\mathbf I - \gamma \mathbf P)\, y > 0 \ \ (y \in \mathbb R^{|\mathcal S|},\ y \ne 0), \qquad z^\top \mathbf A z > 0 \ \ (z \in \mathbb R^d,\ z \ne 0).$$
--
--   This is the conclusion of the book's box: the key matrix and its $\mathbf A$ matrix are positive definite, so on-policy linear TD(0) is stable, and $\mathbf A$ is invertible.
--
--   **Formalization Note** The book leaves two hypotheses implicit and they are stated here: every $\mu(s) > 0$ (without it $\mathbf D(\mathbf I - \gamma \mathbf P)$ is only positive semidefinite) and linearly independent feature columns (without it $\mathbf X z = 0$ for some $z \ne 0$ and $z^\top \mathbf A z = 0$). $\mathbf P$ and the expected rewards are induced by the policy, as the first two lines of the box show. Positive definiteness is in the book's sense for non-symmetric matrices, not Mathlib's `Matrix.PosDef`. Convergence of the stochastic algorithm with probability one, which the book says needs further unstated conditions, is not part of this statement.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, box "Proof of Convergence of Linear TD(0)", pp. 206–207

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

open Matrix

namespace SuttonBartoRL.LinearTD

/-- Sutton & Barto (2018), box "Proof of Convergence of Linear TD(0)", p. 207: in the continuing case
with `0 ≤ γ < 1`, if `µ` is a stationary distribution of the chain induced by `π` with every
`µ(s) > 0` and the feature columns of `X` are linearly independent, then the key matrix `D(I − γP)`
and the `A` matrix (9.11) are both positive definite (`yᵀMy > 0` for `y ≠ 0`). -/
theorem keyMatrix_posDef {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] {d : ℕ}
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (X : Matrix S (Fin d) ℝ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hμ : IsStationaryDist (M.policyTrans π) μ) (hμpos : ∀ s, 0 < μ s)
    (hX : LinearIndependent ℝ Xᵀ) :
    IsPosDefNonsym (keyMatrix μ (M.policyTrans π) γ) ∧ IsPosDefNonsym (tdA M π μ X γ) := by sorry

end SuttonBartoRL.LinearTD
