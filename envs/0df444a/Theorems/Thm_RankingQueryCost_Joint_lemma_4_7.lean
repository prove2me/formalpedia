-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_lemma_4_7
-- name    : RankingQueryCost.Joint.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:27:01.004956+00:00
-- url     : https://prove2.me/theorems/5fd89011-adc6-4d06-910c-5bb6d3226bc4
-- title:
--   Lemma 4.7 — Insertion invariant
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   Start Algorithm 2 after any legal cached history and process labels in public order. After every completed retained-insertion or triple-removal update, its maintained sequence $C$ satisfies
--
--   $$\text{every pair at positional distance at most }s+1\text{ is recorded forward or forced forward}.$$
--
--   The removed triples are vertex-disjoint, and their number is at most $s=a+h$, in every valid world. The state is obtained by running the algorithm; the invariant is not assumed as a state field.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
--   - reading: after each insertion or removal → after each completed retained-insertion or removal update, including its prescribed band scan; reason: the proof establishes a retained insertion after its new band edges have been queried; the intermediate instant before that scan is not claimed
--   - encoding: public ordering of comparisons within pivot and exceptional stars → explicit lexicographic traversal of unordered pair representatives; reason: the source permits a fixed public order; an effective traversal avoids relying on a classically chosen Finset.toList order in the uniform finite-program contract
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 4.7, p. 20, PDF p. 21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Completion
import Definitions.Def_RankingQueryCost_Joint_Pivot

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Lemma 4.7, pp. 20–21 / PDF 21–22, for every completed update of Algorithm 2. -/
theorem lemma_4_7 (n a h : ℕ) (hadm : Admissible n (a + h))
    (W : ComparisonWorld n) (S : InteractionState n) (hS : LegalCachedState a h W S) :
    ∀ m ≤ n,
      let I := insertionThrough (a + h) h m W S
      BandInvariant (a + h) I ∧ (removedVertices I).Nodup ∧ I.triples.length ≤ a + h := by sorry

end RankingQueryCost.Joint
