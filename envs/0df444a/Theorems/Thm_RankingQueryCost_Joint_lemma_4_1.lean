-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_lemma_4_1
-- name    : RankingQueryCost.Joint.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:25:37.040423+00:00
-- url     : https://prove2.me/theorems/cffafa35-6594-456d-9c66-7d0b7180a97a
-- title:
--   Lemma 4.1 — Refinement by reference counts
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   Let a consistent observed pivot tree cover all labels and have terminal width $b$, and acquire full stars at a nonempty reference set. Sort observed reference counts with the pivot-order tie rule to obtain $\sigma$. For every compatible order $r'$, let $g$ be its sorted reference ranks with sentinels. Then
--
--   $$D_2(r',\sigma)\le\Lambda+4s(b-1)^2+24sH(g).$$
--
--   The tree consistency and full stars are conditions on the acquired record, not hypotheses that the reference output is accurate. This is equation (15) in full.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 4.1, p. 15, PDF p. 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Reference

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Lemma 4.1 and equation (15), pp. 15–16 / PDF 16–17. -/
theorem lemma_4_1 (n s b : ℕ) (hadm : Admissible n s) (hb : 1 ≤ b ∧ b ≤ n)
    (T : Transcript n) (P : PivotTree n) (hP : P.Consistent T b)
    (hroot : P.objects = Finset.univ) (S : Finset (Fin n))
    (hne : S.Nonempty) (hstars : StarsPresent T S)
    (r : Rank n) (hr : r ∈ compatible s T) :
    squaredError (referenceOrder T S P.order) (rankVector r) ≤
      (P.leafMass : ℝ) + 4 * s * ((b : ℝ) - 1) ^ 2 +
        24 * s * spacingStatistic S.card (trueReferenceRank r S) := by sorry

end RankingQueryCost.Joint
