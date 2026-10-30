-- Prove2me | Theorems.Thm_SturtRobustStop_Structure_lemma_4
-- name    : SturtRobustStop.Structure.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:12:48.167419+00:00
-- url     : https://prove2.me/theorems/fa5b8349-22bf-4465-a79c-07fd16fe488c
-- title:
--   Lemma 4 — Canonical finite-family policy is a pruned version
-- statement:
--   Let $T,N\ge1$, $d\ge0$, $X=\mathbb R^d$, and let $x^1,\ldots,x^N\in X^T$ be arbitrary sample paths. Let $\epsilon\ge0$ and $g(t,x)$ be arbitrary finite nonnegative full-path rewards, with $g(\infty,x)=0$. Policies have Borel stopping regions $S_t\subseteq X$, and $\tau_\mu(y)=\min\{t:y_t\in S_t\}$, with $\min\varnothing=\infty$. Write $U_t^i=\{z:\|z-x_t^i\|_\infty\le\epsilon\}$, $U^i=\prod_tU_t^i$, $r_i(\mu)=\inf_{y\in U^i}g(\tau_\mu(y),x^i)$, and $J(\mu)=N^{-1}\sum_i r_i(\mu)$.
--
--   A policy is feasible for $(\mathrm{RO}_T)$ when $\forall i\,\exists t\, U_t^i\subseteq S_t$. For such a policy let $\sigma^i(\mu)=\min\{t:U_t^i\subseteq S_t\}$. The assigned policy $\mu^\sigma$ has stopping regions $S_t^\sigma=\bigcup_{j:\sigma^j=t}U_t^j$. A pruned version $\mu'$ of $\mu$ means that $\mu$ is feasible for $(\mathrm{RO}_T)$, $S'_t\subseteq S_t$ for every t, and the earliest full-box stopping minima of both policies agree for each sample. For every feasible $\mu$, choose $\sigma^i=\sigma^i(\mu)$. Then
--   $$\mu^\sigma\text{ is a pruned version of }\mu.$$
--   Both region inclusion and preservation of every earliest full-box stopping minimum are asserted.
--
--   Differences from the source:
--   - encoding: periods and samples numbered from 1, with nonempty horizon and sample → Fin T and Fin N numbered from 0, with T > 0 and N > 0 stored in Model; reason: index k represents source index k+1; all endpoints and the sample-average denominator are preserved
--   - encoding: measurable Stop/Continue maps on the Borel state space → one measurable stopping set per period; reason: a two-action discrete measurable map is equivalent to its measurable Stop preimage
--   - encoding: finite nonnegative full-path rewards and zero reward at infinite stopping time → NNReal finite rewards, Option.some for finite times and Option.none for infinity, extended payoff zero at none; reason: the finite minimum is computed explicitly and the never-stop reward is retained
--   - encoding: finite nonnegative infima, averages and optimal values → ENNReal complete-lattice infima and suprema, with the same average and comparisons; reason: sample boxes contain their centers and their payoff ranges lie in finite sets, giving uniform finite bounds; extended values introduce no new source instances
--   - encoding: a fixed instance of (RO) obtained after simulating sample paths → arbitrary deterministic sample arrays without a probability law; reason: the structural claims hold for any instance of (RO), independently of its sampling law
--   - generalization: a real state vector of finite dimension d → natural dimension d also permits d=0; reason: every positive-dimensional source instance specializes directly; zero dimension is the singleton state space and does not restrict any source instance
-- source:
--   Bradley Sturt, A Nonparametric Algorithm for Optimal Stopping Based on Robust Optimization, arXiv:2103.03300v4, Lemma 4, printed p. 17, PDF p. 17. https://arxiv.org/abs/2103.03300v4

import Definitions.Def_SturtRobustStop_Structure_Pruning

namespace SturtRobustStop.Structure

theorem lemma_4 {T N d : ℕ} (D : Model T N d) (μ : Policy T (State d))
    (hμ : TerminalFeasible D μ) :
    IsPruned D (assignedPolicy D (canonicalAssignment D μ hμ)) μ := by sorry

end SturtRobustStop.Structure
