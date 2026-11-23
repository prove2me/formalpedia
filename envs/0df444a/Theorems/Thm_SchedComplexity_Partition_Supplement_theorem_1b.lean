-- Prove2me | Theorems.Thm_SchedComplexity_Partition_Supplement_theorem_1b
-- name    : SchedComplexity.Partition.Supplement.theorem_1b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:29:23.206893+00:00
-- url     : https://prove2.me/theorems/22c6b496-c231-4284-adbc-75ff1f9f5b83
-- title:
--   Theorem 1(b) — NP-completeness transfers within the scheduling family
-- statement:
--   Let $P'$ and $P$ be any two admissible problems of the Section 3 scheduling family. If $P'$ is polynomial-time many-one reducible to $P$ and $P'$ is NP-complete, then
--
--   $$L(P')\le_p L(P),\quad L(P')\text{ NP-complete}\quad\Longrightarrow\quad L(P)\text{ NP-complete}.$$
--
--   There is no added premise that $P$ belongs to NP. That conclusion is supplied by the paper's preceding NP-membership claim. Both classes range over all admissible machine regimes, shop types, feature sets and criteria.
--
--   Differences from the source:
--   - encoding: recognition problems and polynomial-time reducibility with implicit finite input syntax → binary-coded languages over BSym and CookPvsNP polynomial-time many-one reductions; signed integer thresholds for maximum lateness and natural thresholds otherwise; reason: Sections 2–3 specify integer data and recognition questions; this fixes explicit bit syntax and retains negative lateness
--   - reading: the Section 3 family with ℓ specified only for m>1 and nonnegative operation counts → every label at m=1 is the one-operation single-machine problem; variable m ranges over positive counts; an empty operation list has B_j=C_j=0; reason: the single-machine boundary is explicitly included in 1(c),(k); the empty-list convention extends the published shop completion without imposing a new positivity assumption
--   - reading: λ may contain release and precedence features and their union is used in 1(g),(h) → release levels none < last < all and precedence levels none < tree < arbitrary; all bound and weight restrictions are conjunctive; reason: the proof of 1(g) calls the source a special case of the target, so a union of permissions takes the more general level
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 8, Theorem 1(b)

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

namespace SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem theorem_1b (P' P : Problem) (hP' : P'.Valid) (hP : P.Valid)
    (hred : PolyReducible P'.language P.language) (hcomplete : NPComplete P'.language) :
    NPComplete P.language := by sorry

end SchedComplexity.Partition.Supplement
