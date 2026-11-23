-- Prove2me | Theorems.Thm_SchedComplexity_Partition_Supplement_theorem_1g
-- name    : SchedComplexity.Partition.Supplement.theorem_1g
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:36:20.474115+00:00
-- url     : https://prove2.me/theorems/7b245d24-ba2a-4593-9ae0-9d1240eaab97
-- title:
--   Theorem 1(g) — add release, deadline or precedence features
-- statement:
--   Let $M$ be any fixed positive or variable machine count, $\ell$ any shop type and $k$ any criterion. Let $\lambda'$ contain only arbitrary or last-job release dates, deadlines, arbitrary precedence, or branching precedence, and suppose $(\lambda\cup\lambda',k)$ is admissible. Then
--
--   $$L(M,\ell,\lambda,k)\le_p L(M,\ell,\lambda\cup\lambda',k).$$
--
--   Union takes the more general release or precedence level; every other restriction already in $\lambda$ remains. Deadlines can be added only for makespan or weighted completion time. This states the full special-case reduction, including the need to construct unrestricted input data for the newly allowed feature.
--
--   Differences from the source:
--   - encoding: recognition problems and polynomial-time reducibility with implicit finite input syntax → binary-coded languages over BSym and CookPvsNP polynomial-time many-one reductions; signed integer thresholds for maximum lateness and natural thresholds otherwise; reason: Sections 2–3 specify integer data and recognition questions; this fixes explicit bit syntax and retains negative lateness
--   - reading: the Section 3 family with ℓ specified only for m>1 and nonnegative operation counts → every label at m=1 is the one-operation single-machine problem; variable m ranges over positive counts; an empty operation list has B_j=C_j=0; reason: the single-machine boundary is explicitly included in 1(c),(k); the empty-list convention extends the published shop completion without imposing a new positivity assumption
--   - reading: λ may contain release and precedence features and their union is used in 1(g),(h) → release levels none < last < all and precedence levels none < tree < arbitrary; all bound and weight restrictions are conjunctive; reason: the proof of 1(g) calls the source a special case of the target, so a union of permissions takes the more general level
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, Theorem 1(g)

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

namespace SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem theorem_1g (M : MachineCount) (hM : M.Valid) (ell : ShopKind)
    (lam extra : Parameters) (k : Criterion) (hextra : Generalizations extra)
    (hunion : Admissible (lam ∪ extra) k) :
    PolyReducible (language M ell lam k) (language M ell (lam ∪ extra) k) := by sorry

end SchedComplexity.Partition.Supplement
