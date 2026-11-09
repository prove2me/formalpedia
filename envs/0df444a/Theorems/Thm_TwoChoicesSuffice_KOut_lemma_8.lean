-- Prove2me | Theorems.Thm_TwoChoicesSuffice_KOut_lemma_8
-- name    : TwoChoicesSuffice.KOut.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:18.456399+00:00
-- url     : https://prove2.me/theorems/8293dfa7-4c51-41a0-a866-f2b3b3217daa
-- title:
--   Lemma 8 — recurrence for crossing edges at successive depths
-- statement:
--   Let $G$ be a finite simple graph on $n$ vertices and $H^2=H^2_G$ its random two-out subgraph with replacement. Order vertices by increasing original degree with a fixed tie-break; leaders, owners and depths are taken in $H^2$. For every integer $j\ge0$,
--   $$
--   2\,\mathbb E\bigl[x^j_G(H^2)\bigr]\le n+\mathbb E\bigl[x^{j+1}_G(H^2)\bigr],
--   $$
--   where $x^j_G(H)$ counts the crossing edges of $H$ whose owner (the endpoint in the higher component) is at depth $j$.
--
--   Iterating this recurrence bounds the leaders' crossing edges to lower components (Lemma 9).
--
--   Differences from the source:
--   - generalization: graphs without isolated vertices (standing assumption of §3, PDF p. 7) → any finite simple graph; an isolated vertex makes the single dummy choice, adds no edge, and is counted in n; reason: isolated vertices are singleton components that own no edge and do not change the law on the other vertices, so on graphs without isolates the statement is exactly the source's, and with isolates its right side only grows
--   - encoding: order by increasing original degree, ties broken arbitrarily → ties broken by the LinearOrder instance of V, quantified over every such order; reason: this is the source's 'arbitrary fixed tie-breaking order'; every instance of the source is an instance of the Lean statement
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), Lemma 8, printed p. 10, PDF p. 11

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling
import Definitions.Def_TwoChoicesSuffice_KOut_Leaders

open scoped Classical

namespace TwoChoicesSuffice.KOut

/-- Lemma 8 (PDF p. 11, printed p. 10). For any simple graph `G` and every integer `j ≥ 0`,
`2 E[x^j_G(H^2)] ≤ n + E[x^{j+1}_G(H^2)]`, where `x^j_G(H)` counts the crossing edges of `H`
whose owner (endpoint in the higher component, leaders by increasing original degree with
ties broken by the fixed order of `V`) is at depth `j`, and `H^2` is the random two-out
subgraph with replacement. -/
theorem lemma_8 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (j : ℕ) :
    2 * kOutExpect G 2 (fun σ => (depthCrossing G (prefixGraph G σ 2) j : ℝ)) ≤
      (Fintype.card V : ℝ) +
        kOutExpect G 2 (fun σ => (depthCrossing G (prefixGraph G σ 2) (j + 1) : ℝ)) := by sorry

end TwoChoicesSuffice.KOut
