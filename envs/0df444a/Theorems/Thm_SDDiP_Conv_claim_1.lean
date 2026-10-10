-- Prove2me | Theorems.Thm_SDDiP_Conv_claim_1
-- name    : SDDiP.Conv.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:49:10.559868+00:00
-- url     : https://prove2.me/theorems/123bb74a-5135-42ea-b418-739b2bca17f0
-- title:
--   Claim 1 — exact approximations at the forward solution make the forward tree solution optimal for (2.1)
-- statement:
--   Consider a run of the SND algorithm with valid cuts, lower bounds $L_n\le\mathcal Q_n$ and a solver that returns optimal solutions of the nodal problems. If at iteration $i$
--   $$\psi^i_n(x^i_n) = \mathcal Q_n(x^i_n)\qquad\text{for all } n\in\mathcal T,$$
--   where $\{(x^i_n, y^i_n)\}_{n\in\mathcal T}$ is the forward tree solution (3.6) of iteration $i$, then this forward tree solution is an optimal solution of the multistage program (2.1).
--
--   Claim 1 gives the sufficient condition under which the solution produced by the forward step is optimal; the convergence proof reduces to showing that this condition is eventually met.
--
--   **Formalization Note** Optimality is for the extensive form (2.1) (feasible, and of least cost $\sum_n p_n f_n$ among all feasible tree solutions), not for the DP recursion alone; the paper passes from one to the other without proof.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 475, Claim 1

import Mathlib
import Definitions.Def_SDDiP_Conv_SND

namespace SDDiP.Conv

open StochasticProg.Multistage

/-- Claim 1, p. 475 (Zou–Ahmed–Sun 2019): if at iteration `i` of the SND algorithm (run with valid cuts,
lower bounds under-estimating `𝒬_n`, and a solver returning optimal nodal solutions) the approximations
are exact at the forward solution, `ψ^i_n(x^i_n) = 𝒬_n(x^i_n)` for all `n ∈ T`, then the forward tree
solution `{x^i_n, y^i_n}_{n ∈ T}` is optimal for the extensive form (2.1). -/
theorem claim_1 {H d ℓ M : ℕ} (D : Model H d ℓ) (L : D.T.Node → ℝ)
    (hL : ∀ n x, ¬ D.IsLeaf n → L n ≤ D.Qcal n x)
    (sol : D.Solver) (hsol : D.IsOptimalSolver sol)
    (s : ℕ → Fin M → D.Leaf) (κ : ℕ → D.T.Node → Cut d) (hvalid : D.ValidCuts s κ) (i : ℕ)
    (hexact : ∀ n, D.approx L s κ i n (D.forwardSol L sol s κ i n).1 =
      D.Qcal n (D.forwardSol L sol s κ i n).1) :
    D.IsOptimal (D.forwardSol L sol s κ i) := by sorry

end SDDiP.Conv
