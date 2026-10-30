-- Prove2me | Theorems.Thm_SturtRobustStop_Structure_claim_ec7
-- name    : SturtRobustStop.Structure.claim_ec7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:12:48.577554+00:00
-- url     : https://prove2.me/theorems/22e3dc5e-c7ad-40d2-b0de-b2eccd8d2479
-- title:
--   Claim EC.7 — Constructed policy preserves earliest guaranteed stops
-- statement:
--   Let $T,N\ge1$, $d\ge0$, $X=\mathbb R^d$, and let $x^1,\ldots,x^N\in X^T$ be arbitrary sample paths. Let $\epsilon\ge0$ and $g(t,x)$ be arbitrary finite nonnegative full-path rewards, with $g(\infty,x)=0$. Policies have Borel stopping regions $S_t\subseteq X$, and $\tau_\mu(y)=\min\{t:y_t\in S_t\}$, with $\min\varnothing=\infty$. Write $U_t^i=\{z:\|z-x_t^i\|_\infty\le\epsilon\}$, $U^i=\prod_tU_t^i$, $r_i(\mu)=\inf_{y\in U^i}g(\tau_\mu(y),x^i)$, and $J(\mu)=N^{-1}\sum_i r_i(\mu)$.
--
--   A policy is feasible for $(\mathrm{RO}_T)$ when $\forall i\,\exists t\, U_t^i\subseteq S_t$. For such a policy let $\sigma^i(\mu)=\min\{t:U_t^i\subseteq S_t\}$. The assigned policy $\mu^\sigma$ has stopping regions $S_t^\sigma=\bigcup_{j:\sigma^j=t}U_t^j$. Let $\mu$ be feasible and choose precisely $\sigma^i=\sigma^i(\mu)$, as in the inherited preamble of the proof of Lemma 4. For every sample i,
--   $$\min\{t:U_t^i\subseteq S_t^\sigma\}=\min\{t:U_t^i\subseteq S_t\}.$$
--   These are minima of whole-box stopping periods, rather than the stopping times on the original sample paths. The common value is finite by feasibility.
--
--   Differences from the source:
--   - encoding: periods and samples numbered from 1, with nonempty horizon and sample → Fin T and Fin N numbered from 0, with T > 0 and N > 0 stored in Model; reason: index k represents source index k+1; all endpoints and the sample-average denominator are preserved
--   - encoding: measurable Stop/Continue maps on the Borel state space → one measurable stopping set per period; reason: a two-action discrete measurable map is equivalent to its measurable Stop preimage
--   - encoding: finite nonnegative full-path rewards and zero reward at infinite stopping time → NNReal finite rewards, Option.some for finite times and Option.none for infinity, extended payoff zero at none; reason: the finite minimum is computed explicitly and the never-stop reward is retained
--   - encoding: finite nonnegative infima, averages and optimal values → ENNReal complete-lattice infima and suprema, with the same average and comparisons; reason: sample boxes contain their centers and their payoff ranges lie in finite sets, giving uniform finite bounds; extended values introduce no new source instances
--   - encoding: a fixed instance of (RO) obtained after simulating sample paths → arbitrary deterministic sample arrays without a probability law; reason: the structural claims hold for any instance of (RO), independently of its sampling law
--   - generalization: a real state vector of finite dimension d → natural dimension d also permits d=0; reason: every positive-dimensional source instance specializes directly; zero dimension is the singleton state space and does not restrict any source instance
-- source:
--   Bradley Sturt, A Nonparametric Algorithm for Optimal Stopping Based on Robust Optimization, arXiv:2103.03300v4, Claim EC.7, printed p. ec17, PDF p. 57. https://arxiv.org/abs/2103.03300v4

import Definitions.Def_SturtRobustStop_Structure_Pruning

namespace SturtRobustStop.Structure

theorem claim_ec7 {T N d : ℕ} (D : Model T N d) (μ : Policy T (State d))
    (hμ : TerminalFeasible D μ) :
    ∀ i : Fin N, guaranteedStop D (assignedPolicy D (canonicalAssignment D μ hμ)) i =
      guaranteedStop D μ i := by sorry

end SturtRobustStop.Structure
