-- Prove2me | Theorems.Thm_SDDiP_Conv_theorem_2
-- name    : SDDiP.Conv.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:47:22.512263+00:00
-- url     : https://prove2.me/theorems/2aeec732-2513-4d92-b7a8-a2ed513b0cae
-- title:
--   Theorem 2 — with valid, tight and finite cuts, SND finds an optimal solution of (2.1) after finitely many iterations, almost surely
-- statement:
--   Consider the multistage stochastic mixed integer linear program (2.1) with binary state variables on a finite scenario tree, under (A1) and nodal feasibility for binary parent states. Run the stochastic nested decomposition algorithm (Algorithm 1) with
--   1. sampling with replacement of $M\ge 1$ scenarios per iteration, independently across draws and iterations, according to $\{p_n : n\in S_T\}$;
--   2. lower bounds $L_n$ that under-estimate the expected cost-to-go functions, $L_n\le\mathcal Q_n$ on $\{0,1\}^d$, so that the initial approximation $\psi^1_n = L_n$ is an under-approximation;
--   3. cuts generated in the backward step that are valid (3.4), tight (3.5) and finite;
--   4. a solver of the nodal problems satisfying (A3), i.e. a deterministic map that returns an optimal solution of every nodal problem.
--
--   Then with probability one the forward step of the SND algorithm defines an optimal solution of (2.1) after a finite number of iterations: almost surely there is an iteration $i_0$ such that for every $i\ge i_0$ the forward tree solution $\{(x^i_n, y^i_n)\}_{n\in\mathcal T}$ of (3.6) is an optimal solution of
--   $$\min\Big\{\sum_{n\in\mathcal T} p_n f_n(x_n, y_n) : (x_{a(n)}, x_n, y_n)\in X_n,\ x_n\in\{0,1\}^d\ \ \forall n\in\mathcal T\Big\}.$$
--
--   This is the convergence theorem of the paper: any cut family with the three properties (for instance integer optimality cuts or the Lagrangian cuts of §4.3) makes SND, and its stage-wise independent special case SDDiP, exact for multistage stochastic integer programs with binary states.
--
--   **Formalization Note** "After a finite number of iterations" is read as "from some iteration on, in every iteration" (`∀ᶠ i in atTop`), which is what the proof establishes ($K = \sup\{i : \text{the forward solution is not optimal}\}$ is finite almost surely) and is stronger than "at some iteration". Finiteness of cuts is one finite set for the whole run, as the proof uses it. The cut generator may depend on the sample path, and validity, tightness and finiteness are required along every sample path.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), p. 474, Theorem 2

import Mathlib
import Definitions.Def_SDDiP_Conv_SND

namespace SDDiP.Conv

open StochasticProg.Multistage MeasureTheory Filter

/-- Theorem 2, p. 474 (Zou–Ahmed–Sun, *Stochastic dual dynamic integer programming*, Math. Program. 175
(2019)): if the sampling in the forward step is done with replacement, the cuts generated in the
backward step are valid, tight and finite, and the nodal problems are solved by a deterministic solver
returning optimal solutions (A3), then with probability one the forward step of the SND algorithm
defines an optimal solution of the multistage stochastic program (2.1) after finitely many iterations,
and from then on in every iteration. -/
theorem theorem_2 {H d ℓ M : ℕ} (D : Model H d ℓ) (hM : 0 < M) (L : D.T.Node → ℝ)
    (hL : ∀ n x, ¬ D.IsLeaf n → L n ≤ D.Qcal n x)
    (sol : D.Solver) (hsol : D.IsOptimalSolver sol)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ → Ω → Fin M → D.Leaf) (hS : D.IsSampling P S)
    (κ : Ω → ℕ → D.T.Node → Cut d)
    (hvalid : ∀ ω, D.ValidCuts (fun i => S i ω) (κ ω))
    (htight : ∀ ω, D.TightCuts L sol (fun i => S i ω) (κ ω))
    (hfin : ∀ ω, D.FiniteCuts (fun i => S i ω) (κ ω)) :
    ∀ᵐ ω ∂P, ∀ᶠ i in atTop, D.IsOptimal (D.forwardSol L sol (fun i => S i ω) (κ ω) i) := by sorry

end SDDiP.Conv
