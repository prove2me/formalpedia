-- Prove2me | Theorems.Thm_SchedComplexity_Partition_Supplement_theorem_1h
-- name    : SchedComplexity.Partition.Supplement.theorem_1h
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:37:25.0398+00:00
-- url     : https://prove2.me/theorems/ee87a87d-1b46-4879-85c9-73224491c2a9
-- title:
--   Theorem 1(h) — drop fixed operation, processing or weight restrictions
-- statement:
--   Let $M$ be any fixed positive or variable machine count, $\ell$ any shop type and $k$ any criterion. Let $\lambda'$ contain only a fixed positive operation-count bound, fixed positive lower/upper processing-time bounds, or unit weights. Whenever $(\lambda\cup\lambda',k)$ is admissible,
--
--   $$L(M,\ell,\lambda\cup\lambda',k)\le_p L(M,\ell,\lambda,k).$$
--
--   All positive class constants are quantified, and every restriction in the union is imposed. Removing these restrictions gives the more general recognition problem.
--
--   Differences from the source:
--   - encoding: recognition problems and polynomial-time reducibility with implicit finite input syntax → binary-coded languages over BSym and CookPvsNP polynomial-time many-one reductions; signed integer thresholds for maximum lateness and natural thresholds otherwise; reason: Sections 2–3 specify integer data and recognition questions; this fixes explicit bit syntax and retains negative lateness
--   - reading: the Section 3 family with ℓ specified only for m>1 and nonnegative operation counts → every label at m=1 is the one-operation single-machine problem; variable m ranges over positive counts; an empty operation list has B_j=C_j=0; reason: the single-machine boundary is explicitly included in 1(c),(k); the empty-list convention extends the published shop completion without imposing a new positivity assumption
--   - reading: λ may contain release and precedence features and their union is used in 1(g),(h) → release levels none < last < all and precedence levels none < tree < arbitrary; all bound and weight restrictions are conjunctive; reason: the proof of 1(g) calls the source a special case of the target, so a union of permissions takes the more general level
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, Theorem 1(h)

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

namespace SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem theorem_1h (M : MachineCount) (hM : M.Valid) (ell : ShopKind)
    (lam extra : Parameters) (k : Criterion) (hextra : Restrictions extra)
    (hadm : Admissible (lam ∪ extra) k) :
    PolyReducible (language M ell (lam ∪ extra) k) (language M ell lam k) := by sorry

end SchedComplexity.Partition.Supplement
