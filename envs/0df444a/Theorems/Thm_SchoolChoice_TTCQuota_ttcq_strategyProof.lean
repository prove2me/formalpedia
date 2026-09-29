-- Prove2me | Theorems.Thm_SchoolChoice_TTCQuota_ttcq_strategyProof
-- name    : SchoolChoice.TTCQuota.ttcq_strategyProof
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T08:10:42.480551+00:00
-- url     : https://prove2.me/theorems/2dc44f6d-4ee1-4700-924b-309f91827a6c
-- title:
--   Proposition 7 — the top trading cycles mechanism with type-specific quotas is strategy-proof
-- statement:
--   Let the capacities satisfy the no-shortage condition $|I|\le\sum_s q_s$, and let the type quotas $q_s^t$, the types $\tau$ and the school priorities be arbitrary. Let $P=(P_j)_{j\in I}$ be any profile of announced preferences, let $i$ be a student whose true preference is $P_i$, and let $Q_i$ be any other report. Write $\mathrm{TTC}^q$ for the top trading cycles mechanism with type-specific quotas. If
--   $$\mathrm{TTC}^q(Q_i,P_{-i})(i)=s'\in S,$$
--   then $\mathrm{TTC}^q(P)(i)=s$ for some school $s$ with
--   $$P_i(s)\le P_i(s'),$$
--   that is, $i$ weakly prefers $s$ to $s'$ (rank $0$ is the favourite).
--
--   This is Proposition 7 of the paper: no student can ever benefit by unilaterally misreporting her preferences, whatever the others report. Together with Proposition 6, it shows that the top trading cycles mechanism keeps its incentive property when the district imposes flexible racial or ethnic quotas.
--
--   **Formalization Note** Under the mission's convention for stuck students, the mechanism may leave a student unassigned, which is worse than every school. The statement covers this: if misreporting yields a school, truth-telling yields a school at least as good. Truth-telling is also trivially at least as good when misreporting yields nothing. The others' reports $P_j$, $j\ne i$, are arbitrary, and the misreport is arbitrary. No relation between capacities and type quotas is assumed, which generalises the paper's setting.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), p. 23, Proposition 7 (proof pp. 30–31)

import Mathlib
import Definitions.Def_SchoolChoice_TTCQuota_Algorithm

namespace SchoolChoice.TTCQuota

/-- Proposition 7 (p. 23): the top trading cycles mechanism with type-specific quotas is
strategy-proof. For all capacities `q` with no shortage of seats, all type quotas `qt`,
all student types `τ`, all priorities, every profile of announced preferences `P`, every
student `i` whose true preference is `P i`, and every alternative report `Qi` (the
others' reports unchanged): if `i` is assigned a school `s'` when reporting `Qi`, then
she is assigned a school `s` when reporting `P i`, and she weakly prefers `s` to `s'`
under `P i` (rank `0` is the favourite). -/
theorem ttcq_strategyProof {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] [Fintype Ty] [DecidableEq Ty]
    (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (i : I) (Qi : Pref S) (s' : S)
    (hs' : ttcq q qt τ pri (Function.update P i Qi) i = some s') :
    ∃ s : S, ttcq q qt τ pri P i = some s ∧ P i s ≤ P i s' := by sorry

end SchoolChoice.TTCQuota
