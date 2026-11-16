-- Prove2me | Theorems.Thm_RankingQueryCost_Joint_Supplement_lemma_3_5
-- name    : RankingQueryCost.Joint.Supplement.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:52:24.616011+00:00
-- url     : https://prove2.me/theorems/8b6a4141-f970-4a39-a251-fd021ba981ea
-- title:
--   Lemma 3.5 — Conditional displacement
-- statement:
--   Fix any legal earlier cached history in a fixed-support world, a block $U$ of $m$ objects, its $e$ internal fixed faulty identities, and an integer terminal width $b\ge1$. Fresh uniform pivoting down to width $b$ obeys
--
--   $$\mathbb E[D^2(r_U,\pi)\mid\text{earlier history}]\le C[me+m(b-1)^2].$$
--
--   The constant $C>0$ is absolute and independent of the history, block, world, width and reply strategy. The result holds for every public processing order and every adaptive terminal-bucket completion. The expectation is a finite uniform average over independent pivot priorities drawn after the fixed earlier state. This local error estimate supports Theorem 3.4.
--
--   Differences from the source:
--   - encoding: n labelled objects and ranks 0 through n−1 → Fin n labels and Rank n permutations; reason: a bijective encoding preserving every instance and the full continuous output space Q
--   - encoding: conditional expectation after any earlier history → fix a reachable cached state and average over fresh independent uniform pivot-priority seeds; reason: exactly the conditional experiment, including every cached faulty reply
--   - generalization: the standing admissible comparison domain and adaptive bucket completion → any finite ambient n and fixed support, including empty blocks, with any seed-dependent valid bucket permutation; reason: the proof depends only on m,e,b and bounds every terminal completion simultaneously; restricting to admissible instances and causal completions recovers the printed result
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), Lemma 3.5, p. 10, PDF p. 11

import Definitions.Def_RankingQueryCost_Joint_Supplement_BlockPivot

set_option autoImplicit false

namespace RankingQueryCost.Joint.Supplement

/-- Lemma 3.5, printed p. 10 / PDF 11. Conditioning is represented by
fixing an arbitrary reachable earlier state before sampling a fresh uniform seed.
The finite seed average includes arbitrary adaptive terminal-bucket completions. -/
theorem lemma_3_5 : ∃ C : ℝ, 0 < C ∧
    ∀ (n a b : ℕ) (W : ComparisonWorld n) (S : InteractionState n)
      (U : Finset (Fin n)) (select : BlockSelector n) (finish : BucketCompletion n),
      1 ≤ b → LegalCachedState a 0 W S → ValidCompletion finish →
      let X := fun seed => blockError U W.rank
        (completedOutput finish seed (blockExecution U b n select false W S seed))
      (1 / (Fintype.card (PivotSeed n) : ℝ)) * (∑ seed : PivotSeed n, X seed) ≤
        C * ((U.card : ℝ) * internalFaults U W + U.card * ((b : ℝ) - 1) ^ 2) := by sorry

end RankingQueryCost.Joint.Supplement
