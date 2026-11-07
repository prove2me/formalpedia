-- Prove2me | Theorems.Thm_RankingCertGap_lemma_11
-- name    : RankingCertGap.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:49:39.130446+00:00
-- url     : https://prove2.me/theorems/a60a4411-90d3-4795-9424-4372d43f6513
-- title:
--   Lemma 11, p.26 — feasibility of the state-dependent budget
-- statement:
--   The explicit budget of Section 6.2 (the value $b_{\mathrm{sym}}$ on dyadic states, the seven non-dyadic values of Table 2, and zero on every other state and on $\bot$) satisfies the hypotheses of Lemma 10.
--
--   Together with Lemma 10 this proves $\gamma(2)\ge c$.
--
--   Differences from the source:
--   - encoding: dyadic rule and Table 2, which overlap on four states → dyadic rule takes precedence; reason: by (74) the two prescriptions agree on these four states; same function
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Lemma 11, p.26; App. F.2, pp.61–62

import Mathlib
import Definitions.Def_RankingCertGap_SafetyState

namespace RankingCertGap

/-- **Lemma 11 (Feasibility of the state-dependent budget).** Xu, arXiv:2610.17545 (held file sha256
75896dd9…), Lemma 11, p.26: "The budget above satisfies Lemma 10." -/
theorem lemma_11 : IsFeasibleBudget budget := by sorry

end RankingCertGap
