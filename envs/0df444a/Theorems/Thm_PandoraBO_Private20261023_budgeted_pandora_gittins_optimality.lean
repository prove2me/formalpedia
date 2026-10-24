-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_budgeted_pandora_gittins_optimality
-- name    : PandoraBO.Private20261023.budgeted_pandora_gittins_optimality
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T00:18:15.316927+00:00
-- url     : https://prove2.me/theorems/61bc6ca6-75c2-48fd-860f-027c23f5f9c4
-- title:
--   Theorem 2: Existence of an Optimal Generalized Gittins Policy for Budgeted Pandora's Box
-- statement:
--   Consider a finite nonempty set of boxes $X$. Box $i$ has an independent, integrable real reward $F_i$ and a deterministic opening cost $c_i>0$. Policies are measurable and choose actions using only observed rewards and independent randomization. They must open at least one box, may open each box at most once, and cannot resume after stopping.
--
--   For a policy $\pi$, let $S_\pi$ be the random set of boxes it opens. Define its expected terminal reward and expected total opening cost by
--
--   $$R(\pi)=\mathbb E\!\left[\max_{i\in S_\pi}F_i\right],\qquad C(\pi)=\mathbb E\!\left[\sum_{i\in S_\pi}c_i\right].$$
--
--   The expectation is over the box rewards and the policy's randomization. A fixed **expected budget** $B$ means that a feasible policy satisfies $C(\pi)\le B$. The actual total cost in an individual run may exceed $B$; the constraint bounds its expectation.
--
--   Assume
--
--   $$\min_{i\in X}c_i<B.$$
--
--   There is no upper bound on $B$. For a nonnegative cost multiplier $\lambda$, define the dual objective
--
--   $$A_B(\lambda)=\sup_\rho\{R(\rho)-\lambda C(\rho)\}+\lambda B,$$
--
--   where the supremum ranges over all admissible policies, without imposing the budget constraint. Then there exist a multiplier $\lambda\ge0$ minimizing $A_B$ over $[0,\infty)$ and a generalized Gittins policy $\pi$ such that
--
--   $$\pi\in\arg\max_\rho\{R(\rho)-\lambda C(\rho)\},\qquad C(\pi)\le B,\qquad\lambda(B-C(\pi))=0,$$
--
--   $$\forall\rho,\quad C(\rho)\le B\Longrightarrow R(\rho)\le R(\pi).$$
--
--   Thus $\pi$ maximizes expected reward among all policies satisfying the expected-budget constraint.
--
--   For $\lambda>0$, the index $g_i(\lambda)$ is the unique finite solution of $\mathbb E[(F_i-g_i(\lambda))_+]=\lambda c_i$, where $(x)_+=\max(x,0)$, and the policy spends exactly $C(\pi)=B$ in expectation. For $\lambda=0$, the index is $g_i(0)=\operatorname{ess\,sup}F_i$, possibly $+\infty$, and unused budget is permitted. The index policy first opens a maximal-index box, then opens an unopened maximal-index box when its index exceeds the best observed reward, and stops when the best observed reward exceeds every remaining index. Equality permits either action; ties may be randomized.
--
--   [Paper (arXiv v3)](https://arxiv.org/abs/2406.20062v3). The revised statement formalized here is intended for v4, which will be available on arXiv shortly. No strict reward-gap, bounded-support, continuity, or atomlessness assumption is added. The formal statement and all its proof dependencies have been verified by Prove2Me's Lean 4 server.
-- source:
--   Xie, Astudillo, Frazier, Scully and Terenin. Cost-aware Bayesian Optimization via the Pandora's Box Gittins Index. NeurIPS 2024. Paper (arXiv v3): https://arxiv.org/abs/2406.20062v3. Formalization target: Theorem 2 and Appendix B.5 of the author-revised manuscript intended for arXiv v4, which will be available shortly.

import Definitions.Def_PandoraBO_Model

set_option autoImplicit false

namespace PandoraBO.Private20261023

theorem budgeted_pandora_gittins_optimality {n : ℕ} (M : Instance n)
    (B : ℝ) (hslater : ∃ i : Box n, M.cost i < B) :
    ∃ multiplier : ℝ, dualMinimizer M B multiplier ∧ ∃ π : Policy n,
      isGeneralizedGittinsPolicy M multiplier π ∧ optimal M multiplier π ∧
      complementarySlackness M B multiplier π ∧ budgetOptimal M B π := by sorry

end PandoraBO.Private20261023
