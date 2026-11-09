-- Prove2me | Theorems.Thm_TwoChoicesSuffice_KOut_lemma_9
-- name    : TwoChoicesSuffice.KOut.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:15.304392+00:00
-- url     : https://prove2.me/theorems/b911c4b0-e1f3-4ff9-a3a0-2ecd29c09911
-- title:
--   Lemma 9 — leaders' neighbours in lower components
-- statement:
--   Let $G$ be a finite simple graph on $n$ vertices and $H^2=H^2_G$ its random two-out subgraph with replacement, leaders taken by increasing original degree with a fixed tie-break. Then
--   $$
--   \mathbb E\bigl[L_G(H^2)\bigr]\le n,
--   $$
--   where $L_G(H)$ is the total number of $G$-neighbours of the leaders of $H$ that lie in lower components of $H$.
--
--   Together with the internal neighbours this controls the expected potential of the augmented graph (Lemma 6).
--
--   Differences from the source:
--   - generalization: graphs without isolated vertices (standing assumption of §3, PDF p. 7) → any finite simple graph; an isolated vertex makes the single dummy choice, adds no edge, and is counted in n; reason: isolated vertices are singleton components that own no edge and do not change the law on the other vertices, so on graphs without isolates the statement is exactly the source's, and with isolates its right side only grows
--   - encoding: order by increasing original degree, ties broken arbitrarily → ties broken by the LinearOrder instance of V, quantified over every such order; reason: this is the source's 'arbitrary fixed tie-breaking order'; every instance of the source is an instance of the Lean statement
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), Lemma 9, printed p. 11, PDF p. 12

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling
import Definitions.Def_TwoChoicesSuffice_KOut_Leaders

open scoped Classical

namespace TwoChoicesSuffice.KOut

/-- Lemma 9 (PDF p. 12, printed p. 11). For any simple graph `G`, `E[L_G(H^2)] ≤ n`, where
`L_G(H)` is the total number of `G`-neighbours of the leaders of `H` lying in lower
components of `H` (leaders by increasing original degree, ties by the order of `V`). -/
theorem lemma_9 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) :
    kOutExpect G 2 (fun σ => (leaderLowerNeighbors G (prefixGraph G σ 2) : ℝ)) ≤
      (Fintype.card V : ℝ) := by sorry

end TwoChoicesSuffice.KOut
