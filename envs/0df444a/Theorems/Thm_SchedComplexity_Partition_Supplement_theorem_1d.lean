-- Prove2me | Theorems.Thm_SchedComplexity_Partition_Supplement_theorem_1d
-- name    : SchedComplexity.Partition.Supplement.theorem_1d
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:33:02.826213+00:00
-- url     : https://prove2.me/theorems/d4673ee6-f43d-40af-9080-b8d9d30dd2b4
-- title:
--   Theorem 1(d) — two-machine flow and permutation shops are equivalent
-- statement:
--   For each of the five criteria $k\in\{C_{\max},\sum_jw_jC_j,L_{\max},\sum_jw_jT_j,\sum_jw_jU_j\}$, with no additional features, the two-machine flow-shop and permutation-shop recognition problems are equivalent:
--
--   $$L(2,F,\varnothing,k)\le_p L(2,P,\varnothing,k)\quad\text{and}\quad L(2,P,\varnothing,k)\le_p L(2,F,\varnothing,k).$$
--
--   Both directions are included. The permutation-shop schedule must use one common job permutation on both machines; the flow shop allows different processing orders.
--
--   Differences from the source:
--   - encoding: recognition problems and polynomial-time reducibility with implicit finite input syntax → binary-coded languages over BSym and CookPvsNP polynomial-time many-one reductions; signed integer thresholds for maximum lateness and natural thresholds otherwise; reason: Sections 2–3 specify integer data and recognition questions; this fixes explicit bit syntax and retains negative lateness
--   - reading: the Section 3 family with ℓ specified only for m>1 and nonnegative operation counts → every label at m=1 is the one-operation single-machine problem; variable m ranges over positive counts; an empty operation list has B_j=C_j=0; reason: the single-machine boundary is explicitly included in 1(c),(k); the empty-list convention extends the published shop completion without imposing a new positivity assumption
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, Theorem 1(d)

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

namespace SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem theorem_1d (k : Criterion) :
    PolyReducible (language (.fixed 2) .flow ∅ k) (language (.fixed 2) .permutation ∅ k) ∧
    PolyReducible (language (.fixed 2) .permutation ∅ k) (language (.fixed 2) .flow ∅ k) := by sorry

end SchedComplexity.Partition.Supplement
