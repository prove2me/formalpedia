-- Prove2me | Theorems.Thm_SDDiP_Conv_claim_2
-- name    : SDDiP.Conv.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:47:32.602785+00:00
-- url     : https://prove2.me/theorems/c005e400-d449-4a35-a917-0cbec301c6ab
-- title:
--   Claim 2 — with probability one, no block of unchanged approximations with a non-optimal forward solution is infinite
-- statement:
--   Under the hypotheses of Theorem 2 (sampling with replacement with $M\ge1$, valid, tight and finite cuts, lower bounds $L_n\le\mathcal Q_n$, and a deterministic solver returning optimal nodal solutions), with probability one the following holds: for every iteration $j$, if the approximations stay unchanged from iteration $j$ on,
--   $$\psi^i_n = \psi^j_n\quad\text{on }\{0,1\}^d\qquad\forall n\in\mathcal T,\ \forall i\ge j,$$
--   then the forward tree solution of iteration $j$ is optimal for (2.1).
--
--   This is Claim 2 ("with probability 1, $|I^k_b|$ is finite for all $1\le k\le K_b$"): a maximal block $I^k_b$ of consecutive Type-b iterations (those in which no $\psi_n$ changes) that occurs while the forward solution is not optimal cannot be infinite.
--
--   **Formalization Note** An infinite Type-b block starting at $j$ with a non-optimal forward solution is exactly "all $\psi^i_n$ equal to $\psi^j_n$ for $i\ge j$ while the forward solution of $j$ is not optimal"; the statement excludes it almost surely, which avoids the bookkeeping of $K_a$, $K_b$ and the blocks $I^k_a, I^k_b$.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 475, Claim 2 (Type-b iterations defined on p. 475)

import Mathlib
import Definitions.Def_SDDiP_Conv_SND

namespace SDDiP.Conv

open StochasticProg.Multistage MeasureTheory

/-- Claim 2, p. 475 (Zou–Ahmed–Sun 2019), in the form "a block of Type-b iterations with a non-optimal
forward solution is finite": under the hypotheses of Theorem 2, with probability one there is no
iteration `j` after which all approximations `{ψ^i_n}_{n ∈ T}` stay equal to `{ψ^j_n}_{n ∈ T}` while
the forward tree solution of iteration `j` is not optimal for (2.1). -/
theorem claim_2 {H d ℓ M : ℕ} (D : Model H d ℓ) (hM : 0 < M) (L : D.T.Node → ℝ)
    (hL : ∀ n x, ¬ D.IsLeaf n → L n ≤ D.Qcal n x)
    (sol : D.Solver) (hsol : D.IsOptimalSolver sol)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → Fin M → D.Leaf) (hS : D.IsSampling P S)
    (κ : Ω → ℕ → D.T.Node → Cut d)
    (hvalid : ∀ ω, D.ValidCuts (fun i => S i ω) (κ ω))
    (htight : ∀ ω, D.TightCuts L sol (fun i => S i ω) (κ ω))
    (hfin : ∀ ω, D.FiniteCuts (fun i => S i ω) (κ ω)) :
    ∀ᵐ ω ∂P, ∀ j : ℕ,
      (∀ i ≥ j, D.approx L (fun i => S i ω) (κ ω) i = D.approx L (fun i => S i ω) (κ ω) j) →
        D.IsOptimal (D.forwardSol L sol (fun i => S i ω) (κ ω) j) := by sorry

end SDDiP.Conv
