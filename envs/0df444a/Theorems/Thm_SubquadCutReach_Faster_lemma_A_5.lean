-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_lemma_A_5
-- name    : SubquadCutReach.Faster.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:03:52.186213+00:00
-- url     : https://prove2.me/theorems/a4fffbaa-6a90-455a-940a-458c8cdb5783
-- title:
--   Lemma A.5 — Dependent rounding
-- statement:
--   For every simple hidden graph $H$ and every real fractional orientation rule $z$ on all potential pairs, a uniform zero-error randomized program returns an orientation rule with
--
--   $$\|b_D-b_z\|_\infty\le4,\qquad \mathbb E Q=\widetilde O(n^{5/3}),\qquad Q=\widetilde O(n^{5/3})\text{ with arbitrary fixed polynomial tails}.$$
--
--   The source proof permits four: truncation contributes at most $2n2^{-B}\le2$ for $B=\lceil\log_2 n\rceil$, and the bit contributions sum to less than two. All real fractional inputs are included. There is no correctness exception on a rare tape; retries affect stopping cost. This provides constant error per vertex before exact repair.
--
--   Differences from the source:
--   - encoding: finite labelled oracle inputs and O or Õ bounds → Fin n, finite rational-literal oracle programs, charged queries and outer uniform positive constants; reason: relabeling and an operational cost semantics preserve the source input domain; nontermination has infinite cost
--   - reading: apply balanced orientation to the bit subgraph described as a subgraph of the complete graph → the hidden skeleton intersected with the known odd-bit pair predicate; reason: the following oracle-emulation sentence and the claimed change 2^(1-j)b_Dj require this reading on the existing edges
--   - generalization: O(1) vertex rounding error → vertex error at most 4; reason: the source proof gives at most 2 for downward truncation plus a geometric sum less than 2 for balanced-bit errors; no fractional rule is excluded; the explicit constant implies the O(1) of the source
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 23, Lemma A.5 (PDF p. 25)

import Definitions.Def_SubquadCutReach_Faster_Tasks

set_option autoImplicit false

namespace SubquadCutReach.Faster

/-- The constant 4 is derived from the source proof: <2 truncation and <2 bit error. -/
theorem lemma_A_5 :
    ∃ P : Program, Admissible P ∧ (∀ i : RoundCase, RoundCorrect P i) ∧
      SoftBounds RoundCase (fun i => i.n) (roundCosts P) (fun i => scale i.n) := by sorry

end SubquadCutReach.Faster
