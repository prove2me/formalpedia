-- Prove2me | Theorems.Thm_SturtRobustStop_Structure_theorem_4
-- name    : SturtRobustStop.Structure.theorem_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:12:50.92262+00:00
-- url     : https://prove2.me/theorems/027b5f06-0fb3-4d5e-9a62-d0f8f00af787
-- title:
--   Theorem 4 — Exact optimal attainment by a finite-family stopping policy
-- statement:
--   Let $T,N\ge1$, $d\ge0$, $X=\mathbb R^d$, and let $x^1,\ldots,x^N\in X^T$ be arbitrary sample paths. Let $\epsilon\ge0$ and $g(t,x)$ be arbitrary finite nonnegative full-path rewards, with $g(\infty,x)=0$. Policies have Borel stopping regions $S_t\subseteq X$, and $\tau_\mu(y)=\min\{t:y_t\in S_t\}$, with $\min\varnothing=\infty$. Write $U_t^i=\{z:\|z-x_t^i\|_\infty\le\epsilon\}$, $U^i=\prod_tU_t^i$, $r_i(\mu)=\inf_{y\in U^i}g(\tau_\mu(y),x^i)$, and $J(\mu)=N^{-1}\sum_i r_i(\mu)$.
--
--   The assigned policy $\mu^\sigma$ has stopping regions $S_t^\sigma=\bigcup_{j:\sigma^j=t}U_t^j$. Let $M=\{\mu^\sigma:\sigma\in\{1,\ldots,T\}^N\}$. There exists a measurable $\mu_*\in M$ satisfying
--   $$J(\mu)\le J(\mu_*)\qquad\text{for every Borel measurable Markovian policy }\mu.$$
--   Thus a member of the explicit family attains the unrestricted robust optimum. The result has no approximation factor or error term, and imposes no terminal-feasibility restriction on comparison policies.
--
--   Differences from the source:
--   - encoding: periods and samples numbered from 1, with nonempty horizon and sample → Fin T and Fin N numbered from 0, with T > 0 and N > 0 stored in Model; reason: index k represents source index k+1; all endpoints and the sample-average denominator are preserved
--   - encoding: measurable Stop/Continue maps on the Borel state space → one measurable stopping set per period; reason: a two-action discrete measurable map is equivalent to its measurable Stop preimage
--   - encoding: finite nonnegative full-path rewards and zero reward at infinite stopping time → NNReal finite rewards, Option.some for finite times and Option.none for infinity, extended payoff zero at none; reason: the finite minimum is computed explicitly and the never-stop reward is retained
--   - encoding: finite nonnegative infima, averages and optimal values → ENNReal complete-lattice infima and suprema, with the same average and comparisons; reason: sample boxes contain their centers and their payoff ranges lie in finite sets, giving uniform finite bounds; extended values introduce no new source instances
--   - encoding: a fixed instance of (RO) obtained after simulating sample paths → arbitrary deterministic sample arrays without a probability law; reason: the structural claims hold for any instance of (RO), independently of its sampling law
--   - generalization: a real state vector of finite dimension d → natural dimension d also permits d=0; reason: every positive-dimensional source instance specializes directly; zero dimension is the singleton state space and does not restrict any source instance
--   - encoding: a member of M is optimal for (RO) → existence of a measurable member of the explicitly defined family whose objective dominates every admissible policy; reason: universal dominance by a feasible member is exactly optimal attainment, including equality with the supremum
-- source:
--   Bradley Sturt, A Nonparametric Algorithm for Optimal Stopping Based on Robust Optimization, arXiv:2103.03300v4, Theorem 4, printed p. 16, PDF p. 16. https://arxiv.org/abs/2103.03300v4

import Definitions.Def_SturtRobustStop_Structure_Pruning

namespace SturtRobustStop.Structure

theorem theorem_4 {T N d : ℕ} (D : Model T N d) :
    ∃ μstar : Policy T (State d), μstar ∈ family D ∧
      ∀ μ : Policy T (State d), objective D μ ≤ objective D μstar := by sorry

end SturtRobustStop.Structure
