-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_lemma_5_3
-- name    : SampQueryLB.WarmSLC.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:17:05.528755+00:00
-- url     : https://prove2.me/theorems/d6b4fdbd-c77a-4ae9-be16-7e8bbf253cd1
-- title:
--   Lemma 5.3 — rate window: $|pf(p)-1|\le1/10$ on $p=4,\dots,P$ forces a rate $s_j\in(c/(Q^2p_0),CQ/p_0)$, $c=2^{-20}$, $C=10240$
-- statement:
--   Let $P\ge8$ be even and $1\le q\le Q$ integers. Let
--   $$f(p)=\sum_{j=1}^qc_je^{-s_jp},\qquad c_j\in\mathbb R,\ s_j\ge0,$$
--   satisfy $|pf(p)-1|\le\frac1{10}$ for $p=4,6,\dots,P$.
--
--   **Lemma 5.3.** There exist universal constants $c,C>0$ such that, for every $p_0\in\mathbb R$ with $CQ\le p_0\le cP/Q^2$, some $j$ with $c_j\ne0$ has
--   $$\frac{c}{Q^2p_0}<s_j<\frac{CQ}{p_0};$$
--   one may take $c=2^{-20}$ and $C=10240$.
--
--   The Lean statement is the explicit form with $c=2^{-20}$, $C=10240$, which implies the existential one. Approximating $1/p$ on the even degrees by a short signed exponential sum forces a rate in every such window; this is how passing a gate forces two separated query directions (Lemma 5.4).
--
--   Differences from the source: none.
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 39, Lemma 5.3 (PDF p. 42)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model
import Definitions.Def_SampQueryLB_WarmSLC_HardFamily
import Definitions.Def_SampQueryLB_WarmSLC_Experiments

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory Filter
open scoped ENNReal ContDiff RealInnerProductSpace Topology

namespace SampQueryLB.WarmSLC

theorem lemma_5_3 (P Q q : ℕ) (hP : 8 ≤ P) (hPe : Even P) (hq : 1 ≤ q) (hqQ : q ≤ Q)
    (cs ss : Fin q → ℝ) (hs : ∀ j, 0 ≤ ss j)
    (hf : ∀ p : ℕ, 4 ≤ p → p ≤ P → Even p →
      |(p : ℝ) * ∑ j, cs j * Real.exp (-(ss j * p)) - 1| ≤ 1 / 10)
    (p0 : ℝ) (hp0 : 10240 * (Q : ℝ) ≤ p0) (hp0' : p0 ≤ (2 : ℝ)⁻¹ ^ 20 * P / (Q : ℝ) ^ 2) :
    ∃ j, cs j ≠ 0 ∧ (2 : ℝ)⁻¹ ^ 20 / ((Q : ℝ) ^ 2 * p0) < ss j ∧ ss j < 10240 * Q / p0 := by sorry

end SampQueryLB.WarmSLC
