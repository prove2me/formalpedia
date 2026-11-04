-- Prove2me | Theorems.Thm_PerishBaseStock_Lifetime_lemma_1
-- name    : PerishBaseStock.Lifetime.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:11:47.783187+00:00
-- url     : https://prove2.me/theorems/42498f01-b35b-49b0-a286-08c2e71e966e
-- title:
--   Lemma 1 — $C(S)=h\mathbb E[(S-D)^+]+p\mathbb E[(D-S)^+]+\theta\,\mathbb E[O_\infty(S)]$, independent of the initial state
-- statement:
--   Consider the perishable inventory system with lifetime $m\ge 1$ and FIFO issuance. For a base-stock level $S\ge 0$ let $\bar o(S)$ be the long-run average expected outdating of the base-stock policy $\pi_S$ started from the empty state, the paper's $\mathbb E[O_\infty(S)]$. Then:
--
--   1. the long-run average cost of $\pi_S$ is
--   $$C(S)=h\,\mathbb E[(S-D)^+]+p\,\mathbb E[(D-S)^+]+\theta\,\bar o(S); \tag{3}$$
--   2. the long-run average outdating does not depend on the initial state: for every initial state $\mathbf x_1$ in $\mathcal X=\{0\le x_1\le\dots\le x_{m-1}\le S\}$, the averages $\frac1T\sum_{t=1}^T\mathbb E[o^{\pi_S}_t]$ of the system started at $\mathbf x_1$ **converge** as $T\to\infty$, and the limit is $\bar o(S)$.
--
--   The lemma reduces the cost of a base-stock policy to a newsvendor cost plus $\theta$ times a single average outdating quantity, whether or not the induced Markov chain has a stationary distribution (it can be periodic when $\mathbb P(D<S/m)=1$).
--
--   **Formalization Note** The paper states the existence of a nonnegative random variable $O_\infty(S)$, independent of the initial state, with (3). A bare existence statement would be trivially true, so the lemma is rendered through the mean $\mathbb E[O_\infty(S)]$, which the proof (Appendix A) identifies with the limit of the Cesàro averages of $\mathbb E[o^{\pi_S}_t]$ from every initial state in $\mathcal X$. All quantities are in $[0,\infty]$; averages over $T+1$ periods, $T\in\mathbb N$, are used.
-- source:
--   Bu, Gong & Chao, Asymptotic Optimality of Base-Stock Policies for Perishable Inventory Systems, SSRN 3724966 (accepted manuscript, 2022), p. 9, Lemma 1, (3); pp. ec1–ec3, Appendix A

import Definitions.Def_PerishBaseStock_Lifetime_Model
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace PerishBaseStock.Lifetime

theorem lemma_1 (P : CappedBaseStock.DemandLaw) (c : Params) (S : ℝ≥0) :
    bsCost P c S =
        ENNReal.ofReal (LostSalesOrderUpTo.Asymptotic.backorderCost P.law c.h c.p S) +
          ENNReal.ofReal c.θ * avgOutdate P c.m S ∧
      ∀ x₀ ∈ BSStates c.m S,
        Tendsto (avgOutdateFrom P c.m S x₀) atTop (nhds (avgOutdate P c.m S)) := by sorry

end PerishBaseStock.Lifetime
