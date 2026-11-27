-- Prove2me | Theorems.Thm_SchedComplexity_Partition_Supplement_theorem_1i
-- name    : SchedComplexity.Partition.Supplement.theorem_1i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:40:33.575855+00:00
-- url     : https://prove2.me/theorems/12a4cd2c-27e2-4a80-b65d-44f67a70c583
-- title:
--   Theorem 1(i) — makespan reduces to maximum lateness
-- statement:
--   For every fixed positive or variable machine count $M$, shop type $\ell$ and admissible feature set $\lambda$ without the deadline feature,
--
--   $$L(M,\ell,\lambda,C_{\max})\le_p L(M,\ell,\lambda,L_{\max}).$$
--
--   The paper specifies setting all due dates to zero; this data transformation is the definition `zeroDueDates`. The target uses signed maximum lateness. The exclusion of the deadline feature is the standing Section 3 rule that it is allowed only with makespan or weighted completion time, not an additional restriction on the stated family.
--
--   Differences from the source:
--   - encoding: recognition problems and polynomial-time reducibility with implicit finite input syntax → binary-coded languages over BSym and CookPvsNP polynomial-time many-one reductions; signed integer thresholds for maximum lateness and natural thresholds otherwise; reason: Sections 2–3 specify integer data and recognition questions; this fixes explicit bit syntax and retains negative lateness
--   - reading: the Section 3 family with ℓ specified only for m>1 and nonnegative operation counts → every label at m=1 is the one-operation single-machine problem; variable m ranges over positive counts; an empty operation list has B_j=C_j=0; reason: the single-machine boundary is explicitly included in 1(c),(k); the empty-list convention extends the published shop completion without imposing a new positivity assumption
--   - reading: λ may contain release and precedence features and their union is used in 1(g),(h) → release levels none < last < all and precedence levels none < tree < arbitrary; all bound and weight restrictions are conjunctive; reason: the proof of 1(g) calls the source a special case of the target, so a union of permissions takes the more general level
--   - encoding: λ in a schematic reduction between two criteria → Admissible for the target criterion, which rules out L_max≤0 and retains all positive bounds; reason: Section 3 expressly permits deadlines only for C_max and sumWC, so both sides must be defined
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, Theorem 1(i)

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

namespace SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem theorem_1i (M : MachineCount) (hM : M.Valid) (ell : ShopKind)
    (lam : Parameters) (hadm : Admissible lam .lmax) :
    PolyReducible (language M ell lam .cmax) (language M ell lam .lmax) := by sorry

end SchedComplexity.Partition.Supplement
