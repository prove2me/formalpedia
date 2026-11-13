-- Prove2me | Theorems.Thm_RvsCert_mps23_king_finding
-- name    : RvsCert.mps23_king_finding
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:43:18.027202+00:00
-- url     : https://prove2.me/theorems/f9a8c3f4-5804-4c52-80a3-83a94b8cd63e
-- title:
--   [MPS23] — a king of a tournament can be found with $\tilde O(\sqrt m)$ quantum queries
-- statement:
--   This is an external result (Mande, Paraashar and Saurabh, *Randomized and quantum query complexities of finding a king in a tournament*, FSTTCS 2023), cited by the paper and not proved there.
--
--   There are constants $A$ and $k$ such that for every $m\ge2$ there is a quantum query algorithm, with standard queries to the $\binom m2$ arc bits of a tournament on $m$ vertices, making
--   $$
--   T\ \le\ A\sqrt m\,(\log_2 m+1)^k
--   $$
--   queries, whose measured output is a king of the tournament with probability at least $2/3$, for **every** tournament.
--
--   Differences from the source:
--   - encoding: tournaments on n vertices → m ≥ 2; reason: for m ≤ 1 there are no arc bits and the published QueryAlg model has no algorithm on an empty query register; the lone vertex is trivially the king
--   - reading: find a king in Õ(√n) quantum queries → output a king with probability ≥ 2/3 on every tournament, T ≤ A·√m·(log₂ m + 1)^k with A, k uniform in m; reason: bounded-error worst-case reading of 'find' and of Õ
--   - encoding: an oriented complete graph → arc bits indexed by pairs u < v with standard XOR queries; reason: the input model of the SINK problem on p.4
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 3, p.4, citing [MPS23] (Mande–Paraashar–Saurabh, FSTTCS 2023)

import Mathlib
import Definitions.Def_RvsCert_IsKing
import Definitions.Def_QAlgorithms_Defs_Query

namespace RvsCert

/-- **[MPS23] quantum king finding** (Mande, Paraashar and Saurabh, *Randomized and quantum query
complexities of finding a king in a tournament*, FSTTCS 2023, arXiv:2308.02472; cited on p.4 of
Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1: "one can always find a 'king' in such an oriented complete graph in
Õ(√n) quantum queries"). **External result, not proved in this paper.** There are constants
`A, k` such that for every `m ≥ 2` there is a quantum query algorithm with standard queries to the
`m(m − 1)/2` arc bits, making `T ≤ A·√m·(log₂ m + 1)^k` queries, whose measured output is a
king with probability at least `2/3` on **every** tournament.

**Formalization Note.** `m ≥ 2`: for `m ≤ 1` there are no input bits and the published
`QueryAlg` model has no algorithm on an empty query register; the lone vertex is trivially the
king. -/
theorem mps23_king_finding :
    ∃ (A : ℝ) (k : ℕ), ∀ m : ℕ, 2 ≤ m →
      ∃ (w T : ℕ) (alg : QAlgorithms.QueryAlg (TPair m) Bool (Fin w) T)
        (out : (TPair m × Bool) × Fin w → Fin m),
        (T : ℝ) ≤ A * Real.sqrt m * (Real.logb 2 m + 1) ^ k ∧
        ∀ x : TPair m → Bool,
          2 / 3 ≤ QAlgorithms.probEvent (alg.finalState (QAlgorithms.xorOracle x))
            (fun z => IsKing x (out z)) := by sorry

end RvsCert
