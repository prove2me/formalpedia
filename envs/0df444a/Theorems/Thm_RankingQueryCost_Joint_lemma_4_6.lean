-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_lemma_4_6
-- name    : RankingQueryCost.Joint.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:35.278966+00:00
-- url     : https://prove2.me/theorems/3e2116b4-6595-4d7a-a3fd-2c3d565e20a1
-- title:
--   Lemma 4.6 — Forward-band closure
-- statement:
--   Standing domain: $n\ge16$ is divisible by four, $N=\binom n2$, and the supplied total budget obeys $0\le s\le\lfloor N/32\rfloor$, except for the explicitly generalized band-closure statement. All ranks permute $0,\ldots,n-1$; estimates range over the continuous set $Q$ defined in §2.1.
--
--   Let $C$ be any ordered subset of the labels, represented by an injective ordered list, and let $T$ be a transcript. Put $D=s+1$. If every pair of positions at distance at most $D$ is recorded forward or is forward in every compatible order, then
--
--   $$i<j,\ j-i>D\quad\Longrightarrow\quad r'(C_i)<r'(C_j)\quad\text{for every }r'\in\mathcal C_s(T).$$
--
--   This is a local combinatorial implication about recorded and forced edges. The conclusion does not presume that the unknown order agrees with the whole maintained sequence.
--
--   Differences from the source:
--   - encoding: n labelled objects and unordered distinct comparison identities → Fin n labels and increasing representatives of unordered pairs; reason: this is a bijective representation and leaves the estimate space continuous
--   - generalization: the standing admissible domain n at least 16, divisible by four, with bounded s → all natural n,s and every injectively ordered subset; reason: the edge-disjoint-path argument only uses the s-disagreement budget, so it includes every admissible instance
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 4.6, p. 19, PDF p. 20; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Transcript

set_option autoImplicit false

namespace RankingQueryCost.Joint

/-- Lemma 4.6, p. 19 / PDF 20. The injection is the ordered subset C, so positional
distance is index distance rather than rank distance in an unknown compatible order. -/
theorem lemma_4_6 (n s m : ℕ) (C : Fin m ↪ Fin n) (T : Transcript n)
    (hband : ∀ i j : Fin m, i < j → j.val - i.val ≤ s + 1 →
      RecordedForward T (C i) (C j) ∨ ForcedForward s T (C i) (C j)) :
    ∀ i j : Fin m, i < j → s + 1 < j.val - i.val →
      ForcedForward s T (C i) (C j) := by sorry

end RankingQueryCost.Joint
