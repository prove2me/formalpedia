-- Prove2me | Theorems.Thm_SATotalCoeffLB_section_9_1_graph
-- name    : SATotalCoeffLB.section_9_1_graph
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:17:21.456689+00:00
-- url     : https://prove2.me/theorems/7db21168-69c7-494e-831b-b6f4efa10ff6
-- title:
--   Section 9.1 — a graph on $\lceil m/4\rceil$ vertices with $m$ edges and maximum degree $\le 8$
-- statement:
--   For all sufficiently large $m$, with $n = \lceil m/4 \rceil$, there is a graph on $n$ vertices with exactly $m$ edges, without loops or repeated edges, whose maximum degree is at most eight.
--
--   The edges of this graph are the set $E \subseteq \binom{[n]}{2}$ that indexes the columns of the parity-check matrix $H$ of Lemma 15; the degree bound is what gives Lemma 16.
--
--   Differences from the source:
--   - encoding: for sufficiently large $m$ → there is $M_0$ such that for all $m \ge M_0$; reason: definition
--   - encoding: $n = \lceil m/4 \rceil$; a graph without loops or repeated edges → $n = (m+3)/4$ in natural-number division; a finite set of pairs $i<j$ of $\{0,\dots,n-1\}$, the degree of $v$ being the number of pairs containing $v$; reason: same objects
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Section 9.1, Choice of H, p.50

import Mathlib
import Definitions.Def_SATotalCoeffLB_Pair

namespace SATotalCoeffLB

/-- **Section 9.1, the bounded-degree graph**, p.50 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

For all sufficiently large `m`, with `n = ⌈m/4⌉`, there is a graph on `n` vertices with exactly `m`
edges, no loops or repeated edges, and maximum degree at most eight.

**Formalization Note** `⌈m/4⌉ = (m + 3)/4` in natural-number division. The edges are a finite set
of pairs `i < j` (`Pair n`), which excludes loops and repeated edges; the degree of `v` is the
number of edges containing `v`. -/
theorem section_9_1_graph :
    ∃ M₀ : ℕ, ∀ m ≥ M₀, ∃ E : Finset (Pair ((m + 3) / 4)), E.card = m ∧
      ∀ v : Fin ((m + 3) / 4), (E.filter fun e => e.1.1 = v ∨ e.1.2 = v).card ≤ 8 := by sorry

end SATotalCoeffLB
