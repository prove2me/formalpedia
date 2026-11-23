-- Prove2me | Theorems.Thm_SchedComplexity_Partition_Supplement_theorem_1f
-- name    : SchedComplexity.Partition.Supplement.theorem_1f
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:35:29.350955+00:00
-- url     : https://prove2.me/theorems/977f4054-0d4b-4b30-973e-46a0a96db0bf
-- title:
--   Theorem 1(f) — flow shop reduces to general job shop
-- statement:
--   For any fixed positive or variable machine count $M$, any admissible feature set $\lambda$ and any of the five criteria $k$,
--
--   $$L(M,F,\lambda,k)\le_p L(M,G,\lambda,k).$$
--
--   This is the flow-shop to job-shop special-case relation. No restriction to makespan, to empty features, or to fixed machine counts is imposed; no-wait and bounded-operation features are included when present.
--
--   Differences from the source:
--   - encoding: recognition problems and polynomial-time reducibility with implicit finite input syntax → binary-coded languages over BSym and CookPvsNP polynomial-time many-one reductions; signed integer thresholds for maximum lateness and natural thresholds otherwise; reason: Sections 2–3 specify integer data and recognition questions; this fixes explicit bit syntax and retains negative lateness
--   - reading: the Section 3 family with ℓ specified only for m>1 and nonnegative operation counts → every label at m=1 is the one-operation single-machine problem; variable m ranges over positive counts; an empty operation list has B_j=C_j=0; reason: the single-machine boundary is explicitly included in 1(c),(k); the empty-list convention extends the published shop completion without imposing a new positivity assumption
--   - reading: λ may contain release and precedence features and their union is used in 1(g),(h) → release levels none < last < all and precedence levels none < tree < arbitrary; all bound and weight restrictions are conjunctive; reason: the proof of 1(g) calls the source a special case of the target, so a union of permissions takes the more general level
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, Theorem 1(f)

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

namespace SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem theorem_1f (M : MachineCount) (hM : M.Valid) (lam : Parameters)
    (k : Criterion) (hadm : Admissible lam k) :
    PolyReducible (language M .flow lam k) (language M .general lam k) := by sorry

end SchedComplexity.Partition.Supplement
