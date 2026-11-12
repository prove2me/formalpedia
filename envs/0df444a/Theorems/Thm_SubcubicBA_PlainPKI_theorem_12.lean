-- Prove2me | Theorems.Thm_SubcubicBA_PlainPKI_theorem_12
-- name    : SubcubicBA.PlainPKI.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:43:10.480785+00:00
-- url     : https://prove2.me/theorems/b0a0c444-16db-41ac-9b29-feb2f4d63e71
-- title:
--   Theorem 12 — explicit unbalanced bipartite dispersers
-- statement:
--   There is a constant $d$ and an explicit family of bipartite graphs $G_{n,m}$, for $1\le m\le n$, with left side of size $n$ and right side of size $m$, such that every left vertex has at most $d$ neighbours and $G_{n,m}$ is a bipartite $(n/3,\,5m/6)$-disperser: every set $S$ of at least $n/3$ left vertices has
--   $$|N(S)|\ge\frac{5m}{6}.$$
--   Explicit means that $(n,m)\mapsto G_{n,m}$ (parameters in unary, output the $n\times m$ bit matrix) is computed by a Turing machine in polynomial time.
--
--   PartialValidatedAgreement uses these graphs to hand valid inputs from a third of the parties to most of a smaller set.
--
--   Differences from the source:
--   - encoding: explicit: constructed deterministically in polynomial time (p. 37) → one function from the parameters in unary to the adjacency bit matrix, computed by a Turing machine in polynomial time (TM2ComputableInPolyTime); reason: the paper's definition of explicit; unary parameters make the time polynomial in n
--   - reading: constant left degree (the proof builds a multigraph of left degree 4·3·18) → one constant d, chosen before n and m, bounding the number of distinct neighbours of every left vertex; reason: as a simple graph the merged multigraph has left degree at most d
--   - encoding: (n/3, 5m/6) → real-valued thresholds; the printed statement, not the proof's n/10; reason: same instances; the proof's switch to n/10 is a slip (paper.md item 5)
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), Theorem 12, p. 38

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Graphs

namespace SubcubicBA.PlainPKI

/-- Theorem 12 (p. 38). -/
theorem theorem_12 :
    ∃ d : ℕ, ∃ f : ℕ × ℕ → List Bool, PolyTimeFamily unary2 f ∧
      ∀ n m : ℕ, 1 ≤ m → m ≤ n →
        (f (n, m)).length = n * m ∧
        (∀ u : Fin n, (nbhdOfBits (f (n, m)) n m u).card ≤ d) ∧
        IsBipDisperser (nbhdOfBits (f (n, m)) n m) ((n : ℝ) / 3) (5 * (m : ℝ) / 6) := by sorry

end SubcubicBA.PlainPKI
