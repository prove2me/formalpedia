-- Prove2me | Theorems.Thm_RankingCertGap_lemma_10
-- name    : RankingCertGap.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:54:52.971446+00:00
-- url     : https://prove2.me/theorems/b0926ef7-0d55-4c49-8227-be3eda39271d
-- title:
--   Lemma 10, p.25 — degree-two dual-budget criterion
-- statement:
--   Suppose $b$ assigns a budget to each state in $\mathcal S_2\cup\{\bot\}$ such that $b(\bot)=0$, $b(1,1)=c$, $0\le b(\mathbf s)\le\min\{c,q(\mathbf s)\}$, and every pair of positive input states satisfies
--
--   $$
--   b(\mathbf s_1)+b(\mathbf s_2)-b(\mathbf s_k^+)\le P(\mathbf s_1,\mathbf s_2),\qquad k\in\{1,2\}.
--   $$
--
--   Then $\gamma(2)\ge c$. So a feasible budget on the state space certifies the competitiveness of RANKING on online degree at most two.
--
--   Differences from the source:
--   - encoding: $b$ assigns a budget to each state in $\mathcal S_2\cup\{\bot\}$ → $b$ is a total function on $\texttt{Option State}$, with hypotheses only on $\mathcal S_2\cup\{\bot\}$; reason: its other values are never read, because outputs of two states of $\mathcal S_2$ lie in $\mathcal S_2$
--   - encoding: each instance has an arbitrary online arrival order → $J=\mathrm{Fin}\,n$ listed in arrival order; reason: an arbitrary order is a relabelling of $J$; same instances
--   - encoding: strict rank comparisons, ranks distinct with probability one → a tie goes to the least index among minimum-rank neighbours; reason: ties have probability zero, so no probability or expectation changes
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Lemma 10, p.25; App. F.1, p.60

import Mathlib
import Definitions.Def_RankingCertGap_CertifyingCapacity
import Definitions.Def_RankingCertGap_SafetyState

namespace RankingCertGap

/-- **Lemma 10 (Degree-two dual-budget criterion).** Xu, arXiv:2610.17545 (held file sha256
75896dd9…), Lemma 10, p.25: if `b` assigns a budget to each state in `S₂ ∪ {⊥}` with `b(⊥) = 0`,
`b(1, 1) = c`, `0 ≤ b(s) ≤ min{c, q(s)}`, and every pair of positive input states satisfies (72),
then `γ(2) ≥ c`. -/
theorem lemma_10 (b : Option State → ℝ) (hb : IsFeasibleBudget b) :
    cStar ≤ gammaC (onDegLE 2) := by sorry

end RankingCertGap
