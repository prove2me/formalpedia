-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_lemma_6_1
-- name    : RankingQueryCost.Joint.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:27:38.056202+00:00
-- url     : https://prove2.me/theorems/ad7597b2-4000-429f-80ac-a07dd54d4f13
-- title:
--   Lemma 6.1 — One truncated pivot execution
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   Fix at most $a$ initially faulty identities and at most $h$ online designations, with total supplied budget $s=a+h$. Set $L=\lceil\log_{3/2}n\rceil$ and execute fresh uniform pivots breadth-first through depth $L-1$, finishing remaining blocks by public labels. If $\pi$ is the resulting order and $K(r,\pi)$ its unweighted Kendall inversion count, then
--
--   $$\mathbb EK(r,\pi)\le2aL+6a+n+2nh.$$
--
--   Every execution uses at most $nL$ logical requests and reads each unordered identity at most once within this pivot execution. The statement preserves the printed coefficients and both hard-request clauses.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
--   - encoding: expectation under the stated finite sampling law → the exact finite probability-weighted sum over all masks or independent priority permutations; reason: finite products give precisely the prescribed independent sampling distribution without integrability defaults
--   - encoding: public ordering of comparisons within pivot and exceptional stars → explicit lexicographic traversal of unordered pair representatives; reason: the source permits a fixed public order; an effective traversal avoids relying on a classically chosen Finset.toList order in the uniform finite-program contract
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 6.1, p. 28, PDF p. 29; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Pivot

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Lemma 6.1, pp. 28–29 / PDF 29–30; the exact stated constant K is retained. -/
theorem lemma_6_1 (n a h : ℕ) (hadm : Admissible n (a + h))
    (W : ComparisonWorld n) (hW : LegalWorld a W) :
    (1 / (Fintype.card (PivotSeed n) : ℝ)) *
      (∑ seed : PivotSeed n, (kendallCount W.rank
        (pivotOutput (pivotExecution 1 (pivotDepth n) (fun _ _ => 0) true W h (initialState n) seed)) : ℝ)) ≤
        2 * a * pivotDepth n + 6 * a + n + 2 * n * h ∧
    (∀ seed : PivotSeed n,
      let P := pivotExecution 1 (pivotDepth n) (fun _ _ => 0) true W h (initialState n) seed
      P.requests.length ≤ n * pivotDepth n ∧ P.requests.Nodup) := by sorry

end RankingQueryCost.Joint
