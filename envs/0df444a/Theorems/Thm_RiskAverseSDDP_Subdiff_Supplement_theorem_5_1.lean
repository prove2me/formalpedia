-- Prove2me | Theorems.Thm_RiskAverseSDDP_Subdiff_Supplement_theorem_5_1
-- name    : RiskAverseSDDP.Subdiff.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:34:09.670952+00:00
-- url     : https://prove2.me/theorems/173bff40-908f-4947-a5bb-95200aa40518
-- title:
--   Theorem 5.1 (corrected startup convention) — convergence of Algorithm 2, including (4.34) and Theorem 4.1-(ii)
-- statement:
--   Consider the risk-averse multistage stochastic linear program (5.35)–(5.36) with $T\ge1$ stages, recourse functions $\mathcal Q_t$ and first-stage value $\mathcal Q_1(x_0)$. Assume:
--
--   1. **(H1)**: the process $(\xi_t)$ is interstage independent, $\xi_1$ is deterministic, and for $t=2,\dots,T$ the variable $\xi_t$ has $M$ realizations with probabilities $\Phi_{t,j}>0$ summing to $1$; each $\mathcal P_t$ is a nonempty convex subset of $\{p\ge0:\sum_jp_j\Phi_{t,j}=1\}$;
--   2. **(H3)**: the sampled realizations $\xi^k_t$ (iteration $k\ge1$, stage $t=2,\dots,T$) on a probability space $(\Omega,\mathbb P)$ satisfy $\mathbb P(\xi^k_t=\xi_{t,j})=\Phi_{t,j}$, and $\xi^k_t$ is independent of all samples drawn before it;
--   3. **(H2')**: for every $t=1,\dots,T$, every realization $(\tilde\xi_1,\dots,\tilde\xi_t)$ and every decision sequence $x_{0:t-1}$ feasible on that scenario ($x_\tau\in X_\tau(x_{0:\tau-1},\tilde\xi_\tau)$ for $\tau<t$), the set $X_t(x_{0:t-1},\tilde\xi_t)$ is bounded and nonempty.
--
--   Fix choice rules for Algorithm 2 and, for every $\omega\in\Omega$, a run of Algorithm 2 driven by the samples $\xi^k_t(\omega)$, with decisions $x^k_n$, approximations $\mathcal Q^k_t$ and feasibility cuts. Then for almost every $\omega$, either the run terminates reporting that the problem is infeasible, or both of the following hold:
--
--   1. (4.34) for $t=2,\dots,T$: for every node $n$ of stage $t-1$,
--   $$\lim_{k\to+\infty,\ k\in\tilde{\mathcal S}_n}\ \mathcal Q_t(x^k_{[n]})-\mathcal Q^k_t(x^k_{[n]})=0,$$
--   where $\tilde{\mathcal S}_n=\mathcal S_{P(n)}$ is the set of iterations whose sampled scenario passes through the parent of $n$;
--   2. Theorem 4.1-(ii): the optimal value $\mathfrak Q^k_1(x_0,\xi_1)$ of the first-stage problem (5.41) with the cuts available after iteration $k$ converges to $\mathcal Q_1(x_0)$, and every accumulation point of the first-stage decisions $(x^k_{n_1})_k$ is an optimal solution of (5.36).
--
--   The algorithm is designed for linear programs without relatively complete recourse. The theorem nevertheless assumes the printed (H2''), which supplies nonempty continuations along every feasible history; under that assumption feasibility cuts are never needed.
--
--   **Formalization Note** The dichotomy is stated per sample path, almost surely. The limit along $\tilde{\mathcal S}_n$ is a limit along the filter `atTop ⊓ 𝓟 S̃_n`. All values are extended reals, as in the published Theorem 4.1. Under (H2'), every history the forward pass reaches is feasible on its scenario, so problem (5.37) has value $0$ at every child. Hence no feasibility cut is ever generated and the infeasibility branch never occurs. This is a property of the source's hypotheses. The statement keeps both branches as printed.
--
--   Differences from the source:
--   - reading: "either Algorithm 2 terminates reporting that the problem is infeasible or … (4.34) holds almost surely and Theorem 4.1-(ii) holds" → for almost every sample path, the run reports infeasibility or (4.34) and 4.1-(ii) hold; reason: the paper's proof treats each run this way (it either detects infeasibility or eventually stops generating feasibility cuts and converges a.s.)
--   - generalization: slopes of the feasibility cuts (5.40) and of the optimality cuts (p. 17) given by formulas in optimal Lagrange multipliers → any subgradient of the corresponding optimal-value function at the trial point; reason: the paper states that its formulas give such subgradients (p. 15), and in the linear case this follows from LP duality, so every run of the printed algorithm is a run here
--   - reading: "Theorem 4.1-(ii) holds" for Algorithm 2 → the first-stage value is that of (5.41) at $t=1$ with $\mathcal Q^k_2$ and the feasibility cuts on $x_1$ after iteration $k$, and the decisions are the final first-stage decisions of each iteration; reason: Algorithm 2's first-stage problem includes its feasibility cuts, and the index $k$ versus $k-1$ does not affect the limit
--   - reading: "While there remains a nonvisited child of n" → all children of the current node are examined again at every visit; reason: with persistent visited flags, problem (5.41) could be infeasible after a backtrack and the algorithm would be undefined
--   - reading: $\mathcal P_t$ convex (3.13) → $\mathcal P_t$ convex and nonempty (published `Model.Standing`); reason: $\rho_t$ is a real-valued coherent risk measure, whose dual set is nonempty
--   - encoding: optimal solutions, the vectors $p_k$, the slopes and the order of examining children → values of fixed deterministic choice rules, which must attain the respective optimum; a forward pass is a finite sequence of steps; reason: the convention of the published Algorithm 1 run, which makes the run a function of the samples; under (H2') every forward pass ends after $T$ steps
--   - encoding: extended-real values, 0-based `Fin`/`ℕ` indices for realizations and stages, the limit along $\tilde{\mathcal S}_n$ as a filter limit, and $T\ge1$; reason: Lean conventions; same instances
--   - correction: initial continuation is identically minus infinity, but (5.41) asks for an optimal solution with a finite epigraph variable → choose any feasible minimizer of the extended-real objective while its value is minus infinity; use ordinary minimizers when finite; reason: the initialization on p. 16 and the value-function formulation determine this startup convention; it adds no source assumption and excludes no feasible startup decision
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 17, Theorem 5.1 (with (4.34) of Remark 4.2, p. 14, and Theorem 4.1-(ii), p. 12)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
import Definitions.Def_RiskAverseSDDP_Convergence_Sampling
import Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_LinModel
import Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_Algorithm2
open Filter Topology MeasureTheory ProbabilityTheory

namespace RiskAverseSDDP.Subdiff.Supplement

open RiskAverseSDDP.Convergence

theorem theorem_5_1 {T n M q : ℕ} [NeZero M] (L : LinModel T n M q) (hT : 1 ≤ T)
    (hS : L.toModel.Standing) (hH2' : L.H2') (R : Rules n M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℕ → Fin M) (hH3 : L.toModel.H3 P ξ)
    (r : Ω → RunData n M) (hr : ∀ ω, L.IsRun R (fun k t => ξ k ω t) (r ω)) :
    ∀ᵐ ω ∂P, (r ω).ReportsInfeasible ∨
      ((∀ s, s + 2 ≤ T → ∀ ν : Fin s → Fin M,
          Tendsto
            (fun k => L.toModel.Q (s + 1) ((r ω).hist k s ν) - (r ω).Qm k (s + 1) ((r ω).hist k s ν))
            (atTop ⊓ 𝓟 (tildeIterSet (fun k t => ξ k ω t) s ν)) (𝓝 0)) ∧
        Tendsto (fun k => L.cutVal 0 0 ((r ω).Qm k 1) ((r ω).FC k 0) (Hist.empty n)) atTop
          (𝓝 L.toModel.Q1) ∧
        ∀ xs : EuclideanSpace ℝ (Fin n),
          MapClusterPt xs atTop (fun k => (r ω).x k 0 Fin.elim0) → L.toModel.IsFirstStageOptimal xs) := by sorry

end RiskAverseSDDP.Subdiff.Supplement
