-- Prove2me | Theorems.Thm_RvsCert_sink_unique_king
-- name    : RvsCert.sink_unique_king
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T06:43:10.30159+00:00
-- url     : https://prove2.me/theorems/3ce7d580-d55e-471a-bb32-c713d83d415a
-- title:
--   Section 3 — if a sink exists, the king is unique and equal to the sink
-- statement:
--   Let $x$ be a tournament on $\{0,\dots,m-1\}$ and let $s$ be a sink of $x$ (it beats every other vertex). Then $s$ is a king, and every king of $x$ equals $s$.
--
--   This lets the king-finding algorithm of Mande, Paraashar and Saurabh replace a sink-finding algorithm in the second stage of Lemma 5.
--
--   Differences from the source:
--   - encoding: an orientation of the complete graph, arcs from loser to winner → bits per pair (u < v) with `beats`: bit 1 means u beats v; reason: the arc bits of the SINK input; one fixed convention
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 3, second stage, p.4

import Mathlib
import Definitions.Def_RvsCert_IsSink
import Definitions.Def_RvsCert_IsKing

namespace RvsCert

/-- **Section 3, second stage** (p.4 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): "In a general input, a king is
not unique; however, if a sink exists, then the king is unique and equal to the sink." In every
tournament on `Fin m` with a sink `s`, `s` is a king and every king equals `s`. -/
theorem sink_unique_king (m : ℕ) (x : TPair m → Bool) (s : Fin m) (hs : IsSink x s) :
    IsKing x s ∧ ∀ v : Fin m, IsKing x v → v = s := by sorry

end RvsCert
