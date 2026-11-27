-- Prove2me | Theorems.Thm_SchedComplexity_Partition_Supplement_theorem_1j
-- name    : SchedComplexity.Partition.Supplement.theorem_1j
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:42:17.940491+00:00
-- url     : https://prove2.me/theorems/c0df1d2a-3321-4c8d-aa84-b9da02f486ba
-- title:
--   Theorem 1(j) — weighted completion reduces to weighted tardiness
-- statement:
--   For every fixed positive or variable machine count $M$, shop type $\ell$ and admissible feature set $\lambda$ without the deadline feature,
--
--   $$L(M,\ell,\lambda,\textstyle\sum w_jC_j)\le_p L(M,\ell,\lambda,\textstyle\sum w_jT_j).$$
--
--   The paper specifies setting every due date to zero; this is the definition `zeroDueDates`. Since completion times are nonnegative, tardiness then equals completion time. The exclusion of the deadline feature comes from the source's standing admissibility rule for the target criterion.
--
--   Differences from the source:
--   - encoding: recognition problems and polynomial-time reducibility with implicit finite input syntax → binary-coded languages over BSym and CookPvsNP polynomial-time many-one reductions; signed integer thresholds for maximum lateness and natural thresholds otherwise; reason: Sections 2–3 specify integer data and recognition questions; this fixes explicit bit syntax and retains negative lateness
--   - reading: the Section 3 family with ℓ specified only for m>1 and nonnegative operation counts → every label at m=1 is the one-operation single-machine problem; variable m ranges over positive counts; an empty operation list has B_j=C_j=0; reason: the single-machine boundary is explicitly included in 1(c),(k); the empty-list convention extends the published shop completion without imposing a new positivity assumption
--   - reading: λ may contain release and precedence features and their union is used in 1(g),(h) → release levels none < last < all and precedence levels none < tree < arbitrary; all bound and weight restrictions are conjunctive; reason: the proof of 1(g) calls the source a special case of the target, so a union of permissions takes the more general level
--   - encoding: λ in a schematic reduction between two criteria → Admissible for the target criterion, which rules out L_max≤0 and retains all positive bounds; reason: Section 3 expressly permits deadlines only for C_max and sumWC, so both sides must be defined
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, Theorem 1(j)

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

namespace SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem theorem_1j (M : MachineCount) (hM : M.Valid) (ell : ShopKind)
    (lam : Parameters) (hadm : Admissible lam .sumWT) :
    PolyReducible (language M ell lam .sumWC) (language M ell lam .sumWT) := by sorry

end SchedComplexity.Partition.Supplement
