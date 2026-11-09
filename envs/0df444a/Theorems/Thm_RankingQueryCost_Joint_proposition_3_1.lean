-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_proposition_3_1
-- name    : RankingQueryCost.Joint.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:50.005196+00:00
-- url     : https://prove2.me/theorems/ba8cb9d3-12f2-4ebe-8d0d-6af575c96415
-- title:
--   Proposition 3.1 — Score energy
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   Let $v$ be the win-count vector of a complete table and let $r'$ disagree with at most the supplied $s$ entries. Then
--
--   $$D_2(v,r')\le U.$$
--
--   The identical bound holds for every order compatible with an acquired transcript after any sound forced completion. Both the complete-table and completion clauses are stated. This supplies the finite endpoint error scale.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Proposition 3.1, p. 6, PDF p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Transcript
import Definitions.Def_RankingQueryCost_Joint_Scale

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Proposition 3.1, p. 6 / PDF 7, including sound forced completion. -/
theorem proposition_3_1 (n s : ℕ) (hadm : Admissible n s) :
    (∀ (t : Tournament n) (r : Rank n),
      r ∈ compatible s (completeTranscript t) →
      squaredError (score t) (rankVector r) ≤ (errorScale n s : ℝ)) ∧
    (∀ (T : Transcript n) (t : Tournament n), SoundCompletion s T t →
      ∀ r ∈ compatible s T,
        squaredError (score t) (rankVector r) ≤ (errorScale n s : ℝ)) := by sorry

end RankingQueryCost.Joint
