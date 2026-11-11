-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_lemma_A_4
-- name    : SubquadCutReach.Faster.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:03:55.557258+00:00
-- url     : https://prove2.me/theorems/27b2a7a0-44b9-4786-8ef3-28320010d7ff
-- title:
--   Lemma A.4 — Balanced orientation
-- statement:
--   For every hidden simple graph $J$ on $n$ vertices, one uniform zero-error randomized program computes a known orientation rule whose induced orientation satisfies
--
--   $$|b_D(v)|\le1\quad(\forall v),\qquad \mathbb E Q=\widetilde O(n^{5/3}),\qquad Q=\widetilde O(n^{5/3})\text{ with arbitrary fixed polynomial tails}.$$
--
--   The same finite program uses only neighbour-search, edge-test and vertex-imbalance macros for graph access. Each macro charges its constituent cut queries. Every returning run is correct and termination holds almost surely. This restricted interface permits simulation on hidden subgraphs selected by known bit predicates.
--
--   Differences from the source:
--   - encoding: finite labelled oracle inputs and O or Õ bounds → Fin n, finite rational-literal oracle programs, charged queries and outer uniform positive constants; reason: relabeling and an operational cost semantics preserve the source input domain; nontermination has infinite cost
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 23, Lemma A.4 (PDF p. 25)

import Definitions.Def_SubquadCutReach_Faster_Tasks

set_option autoImplicit false

namespace SubquadCutReach.Faster

theorem lemma_A_4 :
    ∃ P : Program, Admissible P ∧ Restricted P ∧ (∀ i : GraphCase, BalancedCorrect P i) ∧
      SoftBounds GraphCase GraphCase.n (balancedCosts P) (fun i => scale i.n) := by sorry

end SubquadCutReach.Faster
