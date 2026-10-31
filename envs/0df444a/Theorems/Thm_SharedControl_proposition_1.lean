-- Prove2me | Theorems.Thm_SharedControl_proposition_1
-- name    : SharedControl.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:08:41.607121+00:00
-- url     : https://prove2.me/theorems/e59a9311-b34d-4695-9086-fed856432983
-- title:
--   Proposition 1 — under shared control bad proposals are never approved, good ones always iff $\bar r - r_l \le 2\pi_g$
-- statement:
--   Assume the standing assumptions, and let control be shared. Write $m_b = \pi_b + r$ and $s_b = \pi_b - r$ for the payoffs of a bad proposal, $t_s$ for the equilibrium transfer and $P_s = \Pr[m_g \ge t_s]$ for the probability that an uninformed stakeholder approves a good proposal. Then:
--
--   1. **The manager never obtains approval for a bad proposal.** No transfer $t$ makes a bad proposal strictly profitable for the manager, $m_b - t > 0$, and acceptable to the stakeholder: neither to an informed stakeholder ($s_b + t \ge 0$ at the realized $r$) nor to an uninformed one, since for every event $A$ of positive probability on which $m_b - t > 0$,
--   $$
--   E[s_b + t \mid A] < 0 .
--   $$
--   2. **The manager always obtains approval for a good proposal if and only if $\bar r - r_l \le 2\pi_g$:**
--   $$
--   P_s = 1 \iff \bar r - r_l \le 2\pi_g .
--   $$
--
--   Clause 2 is what makes the surplus of shared control sensitive to the stakeholder's information in Proposition 8.
--
--   **Formalization Note** "Approval" of a bad proposal is read as the stakeholder accepting a transfer that leaves the manager strictly better off; conditional expectations are integrals against the conditional measure given a measurable event of positive probability.
--
--   Differences from the source:
--   - reading: the manager never obtains approval for a bad proposal (any proposal that could benefit the manager will be vetoed) → for every t, no ω has mb − t > 0 and sb + t ≥ 0, and for every measurable A with P(A) > 0 on which mb − t > 0, E[sb + t | A] < 0; reason: approval is the stakeholder accepting a transfer under which the manager gains, for an informed and for an uninformed stakeholder
--   - reading: the manager always obtains approval for a good proposal → Ps = Pr[mg ≥ ts] = 1; reason: an informed stakeholder always approves a good proposal (efficient bargaining, p.4), so always is decided by the uninformed case
--   - encoding: E[sg + t | mg ≥ t] in Inequality (1) → the integral of πg − r + t against the conditional measure P[|{mg ≥ t}], with Pr[mg ≥ t] > 0 required for t to satisfy (1); reason: a conditional expectation given a null event is undefined (Lean's cond returns the zero measure there); the least transfer satisfying (1) is unchanged
--   - generalization: r has a continuous distribution with support on [rl, rh], rl the minimum of the support → the law of r is atomless, r ∈ [rl, rh] almost surely, and every set {r < rl + ε}, {rh − ε < r} (ε > 0) has positive probability; reason: these three properties follow from supp(law r) = [rl, rh]; gaps inside (rl, rh) are also allowed, and no density is assumed, so the source's models are a special case
-- source:
--   Meyersson Milgrom, Milgrom, Singh, When Should Control Be Shared?, Management Science (2023), doi:10.1287/mnsc.2022.4356, Proposition 1, p.4

import Mathlib
import Definitions.Def_SharedControl_Model
import Definitions.Def_SharedControl_Standing
import Definitions.Def_SharedControl_Feasible
import Definitions.Def_SharedControl_ts
import Definitions.Def_SharedControl_rbar
import Definitions.Def_SharedControl_Ps

open MeasureTheory ProbabilityTheory

namespace SharedControl

/-- Meyersson Milgrom, Milgrom, Singh, *When Should Control Be Shared?*, Management Science
(2023), doi:10.1287/mnsc.2022.4356, Proposition 1, p.4 (PDF p.5): "Suppose control is shared.
Then, the manager never obtains approval for a bad proposal. The manager always obtains approval
for a good proposal if and only if the parameters satisfy ¯r − rl ≤ 2πg." The first sentence
rests on §2.1, p.4: "When the state is bad, there is no scope for negotiation; any proposal that
could benefit the manager will be vetoed by the stakeholder."

Clause 1 (bad proposals): with `mb = πb + r` and `sb = πb − r`, no transfer `t` makes a bad
proposal strictly profitable for the manager (`mb − t > 0`) and acceptable to the stakeholder,
neither for an informed stakeholder (`sb + t ≥ 0` at the realized `r`) nor for an uninformed one
(conditional expected payoff `E[sb + t | A] ≥ 0` on any event `A` of positive probability on
which the manager gains). Clause 2 (good proposals): `Ps = Pr[mg ≥ ts] = 1` iff
`r̄ − rl ≤ 2πg`.

**Formalization Note.** "Approval" of a bad proposal is read as the stakeholder accepting a
transfer that leaves the manager strictly better off: pointwise for an informed stakeholder,
and in conditional expectation (against `P[|A]`, `A` measurable) for an uninformed one. A good
proposal is always approved by an informed stakeholder (efficient bargaining, p.4), so "always
obtains approval" is `Ps = 1`, the uninformed case (`SharedControl.Ps`). -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : Standing M) :
    ((∀ (ω : Ω) (t : ℝ), ¬ (0 < M.πb + M.r ω - t ∧ 0 ≤ M.πb - M.r ω + t)) ∧
      ∀ (t : ℝ) (A : Set Ω), MeasurableSet A → 0 < M.P A →
        (∀ ω ∈ A, 0 < M.πb + M.r ω - t) →
        ∫ ω, (M.πb - M.r ω + t) ∂(M.P[|A]) < 0) ∧
    (Ps M = 1 ↔ rbar M - M.rl ≤ 2 * M.πg) := by sorry

end SharedControl
