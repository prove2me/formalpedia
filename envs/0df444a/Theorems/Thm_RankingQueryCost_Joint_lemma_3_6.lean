-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_lemma_3_6
-- name    : RankingQueryCost.Joint.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:27:28.815481+00:00
-- url     : https://prove2.me/theorems/acf3b157-b029-4524-be78-34f4567af52d
-- title:
--   Lemma 3.6 — Query potential with online faults
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   After any legal cached history, fresh uniform pivoting to width $1\le b\le n$ in any public order of live-block processing has logical request count $Q$ satisfying
--
--   $$\mathbb EQ\le4[f_b(n)+s],\quad
--   f_b(m)=0\ (m\le b),\quad f_b(m)=m[1+\log_2(m/b)]\ (m>b).$$
--
--   The total budget is $s=a+h$, so this includes fixed, online and intermediate fault splits. The earlier state is operationally reachable, and fresh sampling begins after it is fixed; no clean-event premise is supplied.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
--   - encoding: expectation under the stated finite sampling law → the exact finite probability-weighted sum over all masks or independent priority permutations; reason: finite products give precisely the prescribed independent sampling distribution without integrability defaults
--   - encoding: public ordering of comparisons within pivot and exceptional stars → explicit lexicographic traversal of unordered pair representatives; reason: the source permits a fixed public order; an effective traversal avoids relying on a classically chosen Finset.toList order in the uniform finite-program contract
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 3.6, p. 12, PDF p. 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Pivot

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Lemma 3.6, p. 12 / PDF 13. This covers the intermediate partial-online model as well
as its fixed-support and fully-online endpoints, after every legal cached state. -/
theorem lemma_3_6 (n a h b : ℕ) (hadm : Admissible n (a + h))
    (hb : 1 ≤ b ∧ b ≤ n) (select : BlockSelector n)
    (W : ComparisonWorld n) (S : InteractionState n) (hS : LegalCachedState a h W S) :
    (1 / (Fintype.card (PivotSeed n) : ℝ)) *
      (∑ seed : PivotSeed n,
        ((pivotExecution b n select false W h S seed).requests.length : ℝ)) ≤
      4 * (queryPotential b n + (a + h : ℕ)) := by sorry

end RankingQueryCost.Joint
