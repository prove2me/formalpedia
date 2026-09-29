-- Prove2me | Theorems.Thm_SchoolChoice_TTCQuota_ttcq_constrainedEfficient
-- name    : SchoolChoice.TTCQuota.ttcq_constrainedEfficient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T08:09:26.483686+00:00
-- url     : https://prove2.me/theorems/87a97f05-b63f-493e-87fa-bdef6ede0554
-- title:
--   Proposition 6 — the top trading cycles mechanism with type-specific quotas is constrained efficient
-- statement:
--   Let the capacities satisfy the no-shortage condition $|I|\le\sum_{s} q_s$, and let the type quotas $q_s^t$, the types $\tau$, the priorities and the announced preference profile $P$ be arbitrary. Let $\mu=\mathrm{TTC}^q(P)$ be the outcome of the top trading cycles mechanism with type-specific quotas. Then
--
--   1. $\mu$ satisfies the controlled choice constraints: every school $s$ receives at most $q_s$ students, and at most $q_s^t$ students of each type $t$;
--   2. no assignment $\nu$ satisfying the controlled choice constraints gives every student a weakly better outcome than $\mu$ under $P$ and some student a strictly better one.
--
--   This is Proposition 6 of the paper. Efficiency losses relative to unconstrained Pareto efficiency are unavoidable under type quotas; the proposition says the modified mechanism incurs no loss beyond the one the constraints force.
--
--   **Formalization Note** Outcomes and competitors are assignments that may leave a student unassigned, which is ranked below every school; this is needed for the mission's convention on stuck students (see the definition of the algorithm). When every student is assigned, the statement is exactly the paper's. Efficiency is with respect to the announced preferences. No relation between capacities and type quotas is assumed, which generalises the paper's setting.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), p. 23, Proposition 6 (definition of constrained efficiency pp. 22–23; proof p. 30)

import Mathlib
import Definitions.Def_SchoolChoice_TTCQuota_Algorithm

namespace SchoolChoice.TTCQuota

/-- Proposition 6 (p. 23): the top trading cycles mechanism with type-specific quotas is
constrained efficient. For all capacities `q` with no shortage of seats, all type quotas
`qt`, all student types `τ`, all priorities and every announced preference profile `P`,
the outcome satisfies the controlled choice constraints (capacity and type quotas), and no
other assignment satisfying them makes every student weakly better off and some student
strictly better off under `P` (being unassigned is worse than every school). -/
theorem ttcq_constrainedEfficient {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] [Fintype Ty] [DecidableEq Ty]
    (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) :
    IsConstrainedEfficient q qt τ P (ttcq q qt τ pri P) := by sorry

end SchoolChoice.TTCQuota
