-- Prove2me | Theorems.Thm_SchedComplexity_Partition_Supplement_np_membership
-- name    : SchedComplexity.Partition.Supplement.np_membership
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:28:33.412007+00:00
-- url     : https://prove2.me/theorems/ffd16c66-ab10-48b7-a449-fe0e8171ca11
-- title:
--   Section 4, p. 8 — scheduling recognition belongs to NP
-- statement:
--   Let $P=(M,\ell,\lambda,k)$ be any admissible scheduling problem from Section 3: the machine count may be fixed or variable, every shop type and criterion is allowed, and $\lambda$ can contain any compatible combination of the listed features and fixed positive bounds. Its language of binary-coded recognition yes-instances satisfies
--
--   $$L(P)\in\mathrm{NP}.$$
--
--   This states the membership conclusion of the first paragraph of Section 4, which describes polynomial-depth backtrack search. It supplies the target-membership fact used in Theorem 1(b); membership in NP is not assumed. The schedules are integral and the recognition bound for maximum lateness may be negative.
--
--   Differences from the source:
--   - encoding: recognition problems and polynomial-time reducibility with implicit finite input syntax → binary-coded languages over BSym and CookPvsNP polynomial-time many-one reductions; signed integer thresholds for maximum lateness and natural thresholds otherwise; reason: Sections 2–3 specify integer data and recognition questions; this fixes explicit bit syntax and retains negative lateness
--   - reading: the Section 3 family with ℓ specified only for m>1 and nonnegative operation counts → every label at m=1 is the one-operation single-machine problem; variable m ranges over positive counts; an empty operation list has B_j=C_j=0; reason: the single-machine boundary is explicitly included in 1(c),(k); the empty-list convention extends the published shop completion without imposing a new positivity assumption
--   - reading: λ may contain release and precedence features and their union is used in 1(g),(h) → release levels none < last < all and precedence levels none < tree < arbitrary; all bound and weight restrictions are conjunctive; reason: the proof of 1(g) calls the source a special case of the target, so a union of permissions takes the more general level
--   - reading: can be solved by polynomial-depth backtrack search and thus are members of NP → membership of every admissible binary recognition language in CookPvsNP.NP; reason: the required result is the NP-membership conclusion, with no algorithmic assumption on the scheduling input
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 8, Section 4, p. 8 — every machine scheduling problem of Section 3 is in NP

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

namespace SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem np_membership (P : Problem) (hP : P.Valid) :
    P.language ∈ NP BSym := by sorry

end SchedComplexity.Partition.Supplement
