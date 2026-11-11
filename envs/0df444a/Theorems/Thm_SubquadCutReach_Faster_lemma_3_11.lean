-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_lemma_3_11
-- name    : SubquadCutReach.Faster.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:04:10.24113+00:00
-- url     : https://prove2.me/theorems/7bdc1798-8b06-4d1c-bfd1-f78d3517511f
-- title:
--   Lemma 3.11 — Cut-query repair
-- statement:
--   Let $H$ be hidden, $b^*$ an existentially feasible target, and $D$ any known all-pair orientation rule. One uniform deterministic program returns another known rule $D'$ with
--
--   $$b_{D'}=b^*,\qquad Q\le C\left(n^{5/3}+n\sqrt{\|b_D-b^*\|_1}\right)L(n)^p.$$
--
--   The constants precede every input. Only cut access to $H$ is available, and the returned finite table can be evaluated without further queries. This is exact repair, including zero discrepancy; feasibility supplies no algorithmic witness.
--
--   Differences from the source:
--   - encoding: finite labelled oracle inputs and O or Õ bounds → Fin n, finite rational-literal oracle programs, charged queries and outer uniform positive constants; reason: relabeling and an operational cost semantics preserve the source input domain; nontermination has infinite cost
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 11, Lemma 3.11 (PDF p. 13)

import Definitions.Def_SubquadCutReach_Faster_Tasks

set_option autoImplicit false

namespace SubquadCutReach.Faster

theorem lemma_3_11 :
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∃ P : Program, Admissible P ∧ Deterministic P ∧
      ∀ i : RepairCase, RunsWithin P (cut i.H) (repairInput i.b i.D)
        (fun m => imbalance (induced i.H (outputRule i.n m)) = i.b)
        (C*(scale i.n+i.n*Real.sqrt (error i.H i.D i.b))*L i.n^p) := by sorry

end SubquadCutReach.Faster
