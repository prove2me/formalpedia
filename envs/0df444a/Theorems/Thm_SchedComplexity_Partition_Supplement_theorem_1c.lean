-- Prove2me | Theorems.Thm_SchedComplexity_Partition_Supplement_theorem_1c
-- name    : SchedComplexity.Partition.Supplement.theorem_1c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:30:39.460169+00:00
-- url     : https://prove2.me/theorems/971a88f9-1fd7-4c9a-ba3e-ff42cf3609b4
-- title:
--   Theorem 1(c) — increase the machine count or make it variable
-- statement:
--   Let $m'\ge1$ be any fixed machine count, let $\ell$ be any shop type, and let $(\lambda,k)$ be any admissible feature/criterion pair. For any fixed $m\ge m'$, and also for variable machine count,
--
--   $$L(m',\ell,\lambda,k)\le_p L(m,\ell,\lambda,k),\qquad L(m',\ell,\lambda,k)\le_p L(\mathrm{variable},\ell,\lambda,k).$$
--
--   The result includes the single-machine source, identical parallel machines, no wait and bounded positive processing times. It asserts polynomial-time reducibility of the recognition problems, not a promise that the original instance remains unchanged or belongs literally to the larger-machine class. The source calls the proof trivial; the full schematic claim is retained.
--
--   Differences from the source:
--   - encoding: recognition problems and polynomial-time reducibility with implicit finite input syntax → binary-coded languages over BSym and CookPvsNP polynomial-time many-one reductions; signed integer thresholds for maximum lateness and natural thresholds otherwise; reason: Sections 2–3 specify integer data and recognition questions; this fixes explicit bit syntax and retains negative lateness
--   - reading: the Section 3 family with ℓ specified only for m>1 and nonnegative operation counts → every label at m=1 is the one-operation single-machine problem; variable m ranges over positive counts; an empty operation list has B_j=C_j=0; reason: the single-machine boundary is explicitly included in 1(c),(k); the empty-list convention extends the published shop completion without imposing a new positivity assumption
--   - reading: λ may contain release and precedence features and their union is used in 1(g),(h) → release levels none < last < all and precedence levels none < tree < arbitrary; all bound and weight restrictions are conjunctive; reason: the proof of 1(g) calls the source a special case of the target, so a union of permissions takes the more general level
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, Theorem 1(c)

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

namespace SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem theorem_1c (m' : ℕ) (hm' : 0 < m') (M : MachineCount)
    (hcounts : (∃ m, M = .fixed m ∧ m' ≤ m) ∨ M = .variable)
    (ell : ShopKind) (lam : Parameters) (k : Criterion) (hadm : Admissible lam k) :
    PolyReducible (language (.fixed m') ell lam k) (language M ell lam k) := by sorry

end SchedComplexity.Partition.Supplement
