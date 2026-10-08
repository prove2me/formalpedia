-- Prove2me | Theorems.Thm_SuttonBartoRL_LinearTD_keyMatrix_colSums
-- name    : SuttonBartoRL.LinearTD.keyMatrix_colSums
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:48:03.378171+00:00
-- url     : https://prove2.me/theorems/2dbb75c3-b282-4945-990b-80b279ca230c
-- title:
--   Column sums of the key matrix, $\mathbf 1^\top\mathbf D(\mathbf I - \gamma\mathbf P) = (1-\gamma)\boldsymbol\mu^\top$
-- statement:
--   Let a finite MDP and a policy $\pi$ be given, let $\mathbf P$ be the transition matrix of the chain induced by $\pi$, let $\boldsymbol\mu$ be a vector with $\boldsymbol\mu^\top \mathbf P = \boldsymbol\mu^\top$ (that is, $\boldsymbol\mu = \mathbf P^\top \boldsymbol\mu$, as for a stationary distribution) and $\mu(s) > 0$ for every state $s$, let $\mathbf D = \mathrm{diag}(\boldsymbol\mu)$, and let $\gamma < 1$. Then the row vector of column sums of the key matrix is
--
--   $$\mathbf 1^\top \mathbf D(\mathbf I - \gamma \mathbf P) = \boldsymbol\mu^\top(\mathbf I - \gamma \mathbf P) = \boldsymbol\mu^\top - \gamma \boldsymbol\mu^\top \mathbf P = \boldsymbol\mu^\top - \gamma\boldsymbol\mu^\top = (1 - \gamma)\boldsymbol\mu^\top,$$
--
--   all components of which are positive.
--
--   Together with the positive row sums, this is what makes the key matrix positive definite by the criterion of Sutton (1988).
--
--   **Formalization Note** The identity uses only $\boldsymbol\mu^\top \mathbf P = \boldsymbol\mu^\top$; positivity of the components uses $\gamma < 1$ and $\mu(s) > 0$, the latter a hypothesis the book leaves implicit (it holds for the stationary distribution of an irreducible chain).
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, box "Proof of Convergence of Linear TD(0)", p. 207

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

open Matrix

namespace SuttonBartoRL.LinearTD

/-- Sutton & Barto (2018), box "Proof of Convergence of Linear TD(0)", p. 207: if `µ` is stationary,
`µᵀP = µᵀ`, the column sums of the key matrix `D(I − γP)` are `1ᵀD(I − γP) = (1 − γ)µᵀ`, all of
whose components are positive when `γ < 1` and every `µ(s) > 0`. -/
theorem keyMatrix_colSums {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (μ : S → ℝ) (γ : ℝ)
    (hγ1 : γ < 1) (hμpos : ∀ s, 0 < μ s) (hstat : vecMul μ (M.policyTrans π) = μ) :
    vecMul (fun _ => (1 : ℝ)) (keyMatrix μ (M.policyTrans π) γ) = (1 - γ) • μ ∧
      ∀ s, 0 < vecMul (fun _ => (1 : ℝ)) (keyMatrix μ (M.policyTrans π) γ) s := by sorry

end SuttonBartoRL.LinearTD
