-- Prove2me | Theorems.Thm_SchedComplexity_Partition_Supplement_theorem_1e
-- name    : SchedComplexity.Partition.Supplement.theorem_1e
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:34:41.867481+00:00
-- url     : https://prove2.me/theorems/57535a40-c040-4a7f-963d-462f7d981d3e
-- title:
--   Theorem 1(e) — three-machine flow and permutation makespan are equivalent
-- statement:
--   For makespan, and with no additional features, the three-machine flow-shop and permutation-shop recognition problems are equivalent:
--
--   $$L(3,F,\varnothing,C_{\max})\le_p L(3,P,\varnothing,C_{\max})\quad\text{and}\quad L(3,P,\varnothing,C_{\max})\le_p L(3,F,\varnothing,C_{\max}).$$
--
--   Both directions are included. This part concerns only makespan; Theorem 1(d) is the corresponding two-machine statement for every criterion.
--
--   Differences from the source:
--   - encoding: recognition problems and polynomial-time reducibility with implicit finite input syntax → binary-coded languages over BSym and CookPvsNP polynomial-time many-one reductions; signed integer thresholds for maximum lateness and natural thresholds otherwise; reason: Sections 2–3 specify integer data and recognition questions; this fixes explicit bit syntax and retains negative lateness
--   - reading: the Section 3 family with ℓ specified only for m>1 and nonnegative operation counts → every label at m=1 is the one-operation single-machine problem; variable m ranges over positive counts; an empty operation list has B_j=C_j=0; reason: the single-machine boundary is explicitly included in 1(c),(k); the empty-list convention extends the published shop completion without imposing a new positivity assumption
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, Theorem 1(e)

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

namespace SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem theorem_1e :
    PolyReducible (language (.fixed 3) .flow ∅ .cmax)
      (language (.fixed 3) .permutation ∅ .cmax) ∧
    PolyReducible (language (.fixed 3) .permutation ∅ .cmax)
      (language (.fixed 3) .flow ∅ .cmax) := by sorry

end SchedComplexity.Partition.Supplement
