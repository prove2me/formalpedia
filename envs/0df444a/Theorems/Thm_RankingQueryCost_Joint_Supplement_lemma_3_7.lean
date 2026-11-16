-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_Supplement_lemma_3_7
-- name    : RankingQueryCost.Joint.Supplement.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:52:55.984829+00:00
-- url     : https://prove2.me/theorems/7d164991-df14-4c25-96c2-25677e31d1fb
-- title:
--   Lemma 3.7 — Depth-truncated pivoting
-- statement:
--   Fix any legal earlier cached history in a fixed-support world, a block $U$ of $m$ objects with $e$ internal fixed faulty identities, integer width $b\ge1$, and depth cap $L\ge0$. Process fresh uniform pivots breadth first, stop at size at most $b$ or depth $L$, and complete terminal blocks by public identifiers. Then
--
--   $$\mathbb E[D^2(r_U,\pi_{\rm tr})\mid H_0]\le C_{\rm tr}[me+m(b-1)^2+2^{-L}m^3].$$
--
--   On every fresh seed the execution uses at most $mL$ requests and at most $\binom m2$ new identities. The constant is absolute and independent of every earlier history and reply strategy. Cached reads count as requests. The expectation is a finite uniform average. This supplies all three conclusions needed for depth-truncated resolution in Theorem 3.4.
--
--   Differences from the source:
--   - encoding: n labelled objects and ranks 0 through n−1 → Fin n labels and Rank n permutations; reason: a bijective encoding preserving every instance and the full continuous output space Q
--   - encoding: conditional expectation and two hard execution caps → a finite average after a reachable cached state, the request-list length, and the new-ledger set difference; reason: fresh randomness is independent of the earlier history; the caps distinguish requests from new identities
--   - generalization: the standing admissible comparison domain → any finite ambient n and fixed support, including empty blocks; reason: the conditional proof depends only on m,e,b,L and remains valid without the global admissibility restrictions
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 3.7, p. 12, PDF p. 13

import Definitions.Def_RankingQueryCost_Joint_Supplement_BlockPivot

set_option autoImplicit false

namespace RankingQueryCost.Joint.Supplement

/-- Lemma 3.7, printed p. 12 / PDF 13. All three conclusions hold after
every legal earlier history; the request list counts cached reads as requests. -/
theorem lemma_3_7 : ∃ Ctr : ℝ, 0 < Ctr ∧
    ∀ (n a b L : ℕ) (W : ComparisonWorld n) (S : InteractionState n) (U : Finset (Fin n)),
      1 ≤ b → LegalCachedState a 0 W S →
      let P := fun seed => blockExecution U b L breadthFirst true W S seed
      let X := fun seed => blockError U W.rank (identifierOutput (P seed))
      (1 / (Fintype.card (PivotSeed n) : ℝ)) * (∑ seed : PivotSeed n, X seed) ≤
        Ctr * ((U.card : ℝ) * internalFaults U W + U.card * ((b : ℝ) - 1) ^ 2 +
          (2 : ℝ) ^ (-(L : ℤ)) * (U.card : ℝ) ^ 3) ∧
      ∀ seed, (P seed).requests.length ≤ U.card * L ∧
        ((acquired (P seed).interaction.ledger) \ acquired S.ledger).card ≤ U.card.choose 2 := by sorry

end RankingQueryCost.Joint.Supplement
