-- Prove2me | Theorems.Thm_TwoChoicesSuffice_KOut_lemma_16
-- name    : TwoChoicesSuffice.KOut.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:19.308922+00:00
-- url     : https://prove2.me/theorems/5fb9ce83-8c2a-4a6f-977f-f787066ea094
-- title:
--   Lemma 16 — marked and unmarked depth recurrences, (10) and (11)
-- statement:
--   Let $G$ be a finite simple graph on $n$ vertices. Under the marked two-out law, let $B=B(\sigma,S)$ be the base graph, with owners, leaders and depths for the relevant-degree order (increasing $d_v$, ties by a fixed order $\pi$), and let $M_j(B)$, $N_j(B)$ count the allowed crossing edges of $B$ owned at depth $j$ by a marked, respectively unmarked, vertex, $T_j=M_j+N_j$. For every integer $j\ge0$, both
--   $$
--   \mathbb E[T_j(B)]\le\frac87n+\frac87\,\mathbb E[M_{j+1}(B)]+\frac47\,\mathbb E[N_{j+1}(B)]\qquad(10)
--   $$
--   and
--   $$
--   \mathbb E[M_j(B)]\le\frac47n+\frac47\,\mathbb E[N_{j+1}(B)]\qquad(11)
--   $$
--   hold.
--
--   Solving these recurrences backwards in $j$ bounds the leaders' neighbours in lower components of $B$ (proof of Lemma 15).
--
--   Differences from the source:
--   - generalization: graphs without isolated vertices (standing assumption of §3, PDF p. 7) → any finite simple graph; an isolated vertex makes the single dummy choice, adds no edge, and is counted in n; reason: isolated vertices are singleton components that own no edge and do not change the law on the other vertices, so on graphs without isolates the statement is exactly the source's, and with isolates its right side only grows
--   - encoding: a fixed total order π chosen independently of the sample and colouring → the LinearOrder instance of V, universally quantified; reason: a fixed deterministic order is independent of the randomness; every choice of π is covered
-- source:
--   Yanyu Chen, Yu Chen, STOC 2027 submission #372 (October 2026), Lemma 16, printed p. 21, PDF p. 22

import Mathlib
import Definitions.Def_TwoChoicesSuffice_KOut_Sampling
import Definitions.Def_TwoChoicesSuffice_KOut_Leaders
import Definitions.Def_TwoChoicesSuffice_KOut_Coloring
import Definitions.Def_TwoChoicesSuffice_KOut_Marked

open scoped Classical

namespace TwoChoicesSuffice.KOut

/-- Lemma 16 (PDF p. 22, printed p. 21). Under the marked two-out law, for every integer
`j ≥ 0`, with `M_j, N_j, T_j = M_j + N_j` the allowed crossing edges of the base graph `B`
owned at depth `j` by a marked, an unmarked, resp. any vertex (relevant-degree order):
(10) `E[T_j(B)] ≤ (8/7) n + (8/7) E[M_{j+1}(B)] + (4/7) E[N_{j+1}(B)]`, and
(11) `E[M_j(B)] ≤ (4/7) n + (4/7) E[N_{j+1}(B)]`. -/
theorem lemma_16 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (j : ℕ) :
    markedExpect G (fun σ S => (totalDepth G σ S j : ℝ)) ≤
        (8 / 7 : ℝ) * (Fintype.card V : ℝ) +
          (8 / 7 : ℝ) * markedExpect G (fun σ S => (markedDepth G σ S (j + 1) : ℝ)) +
          (4 / 7 : ℝ) * markedExpect G (fun σ S => (unmarkedDepth G σ S (j + 1) : ℝ)) ∧
      markedExpect G (fun σ S => (markedDepth G σ S j : ℝ)) ≤
        (4 / 7 : ℝ) * (Fintype.card V : ℝ) +
          (4 / 7 : ℝ) * markedExpect G (fun σ S => (unmarkedDepth G σ S (j + 1) : ℝ)) := by sorry

end TwoChoicesSuffice.KOut
