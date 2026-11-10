-- Prove2me | Theorems.Thm_SivanLPTensor_Recovery_unique_rank_decomposition
-- name    : SivanLPTensor.Recovery.unique_rank_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T05:33:10.278192+00:00
-- url     : https://prove2.me/theorems/52933400-4f8b-4a2a-a08d-958c6bcb9324
-- title:
--   Lemma 5.1 — Uniqueness and minimum rank
-- statement:
--   Let $m\ge3$, let every $n_j$ be positive, and let $r>0$ nonzero factor terms give $T$ and satisfy LP. Then
--   $$\operatorname{rank}(T)=r,$$
--   and every $r$-term decomposition of $T$ into nonzero pure tensors agrees with the given one up to one common permutation and component scalings whose product is one in each term.
--   The competing decomposition need not satisfy LP. The minimum-rank clause compares against every number of nonzero terms. This statement supplies uniqueness independently of the recovery theorem and has no import of Theorem 3.4 or 1.1.
--
--   Differences from the source:
--   - encoding: finite real modes and one-based indices → dependent Fin coordinates with zero-based indices; reason: the same finite arrays; parity in the signed minor formula is unchanged
-- source:
--   Shiri Sivan, STOC 2027 submission #1294 (October 2026), Lemma 5.1, printed p. 13 / PDF p. 15

import Definitions.Def_SivanLPTensor_Recovery_geometryModel

namespace SivanLPTensor.Recovery
open scoped BigOperators

theorem unique_rank_decomposition {m r : ℕ} {n : Fin m → ℕ}
    (hm : 3 ≤ m) (hn : ∀ j, 0 < n j) (hr : 0 < r)
    (a : Factors n r) (ha : NonzeroFactors a) (hLP : LP a) :
    UniqueRank a := by sorry

end SivanLPTensor.Recovery
