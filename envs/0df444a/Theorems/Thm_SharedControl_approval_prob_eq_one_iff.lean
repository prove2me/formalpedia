-- Prove2me | Theorems.Thm_SharedControl_approval_prob_eq_one_iff
-- name    : SharedControl.approval_prob_eq_one_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:07:32.011697+00:00
-- url     : https://prove2.me/theorems/b461a710-6fad-4d12-be6b-ad7e00b8913f
-- title:
--   Proof of Proposition 1, p.4 — $\Pr[m_g \ge t] = 1$ iff $t \le \pi_g + r_l$
-- statement:
--   Assume the standing assumptions. For every real threshold $t$,
--
--   $$
--   \Pr[m_g \ge t] = \Pr[\pi_g + r \ge t] = 1 \iff t \le \pi_g + r_l .
--   $$
--
--   At $t = t_s$ this is the last step of the proof of Proposition 1: if $t_s > \pi_g + r_l$, the realizations $r_l \le r < t_s - \pi_g$ have positive probability, and for them the good proposal is not implemented; if $t_s \le \pi_g + r_l$, the offer is made for almost every realization.
--
--   Differences from the source:
--   - generalization: the step for the threshold ts → every real threshold t; reason: the instance t = ts is the source's step
--   - reading: for realizations of r such that rl ≤ r < ts − πg, the proposal is not implemented → Pr[mg ≥ t] = 1 iff t ≤ πg + rl; reason: the sentence asserts that the good proposal fails with positive probability when ts > πg + rl; the equivalence states this together with the converse used in the first half of the proof
--   - generalization: r has a continuous distribution with support on [rl, rh], rl the minimum of the support → the law of r is atomless, r ∈ [rl, rh] almost surely, and every set {r < rl + ε}, {rh − ε < r} (ε > 0) has positive probability; reason: these three properties follow from supp(law r) = [rl, rh]; gaps inside (rl, rh) are also allowed, and no density is assumed, so the source's models are a special case
-- source:
--   Meyersson Milgrom, Milgrom, Singh, When Should Control Be Shared?, Management Science (2023), doi:10.1287/mnsc.2022.4356, proof of Proposition 1, p.4

import Mathlib
import Definitions.Def_SharedControl_Model
import Definitions.Def_SharedControl_Standing

open MeasureTheory

namespace SharedControl

/-- Meyersson Milgrom, Milgrom, Singh, *When Should Control Be Shared?*, Management Science
(2023), doi:10.1287/mnsc.2022.4356, proof of Proposition 1, p.4 (PDF p.5): "Therefore, for
realizations of r such that rl ≤ r < ts − πg, the proposal is not implemented."

A transfer `t` is accepted for almost all realizations of `r`, i.e. `Pr[mg ≥ t] = 1` with
`mg = πg + r`, if and only if `t ≤ πg + rl`. At `t = ts` this is the step of the proof: if
`ts > πg + rl`, the realizations `rl ≤ r < ts − πg` have positive probability and the good
proposal is not implemented there.

**Formalization Note.** Stated for every real threshold `t`, not only for `ts`; the paper's
step is the instance `t = ts`. The probability is the measure of the event in `ℝ≥0∞`. -/
theorem approval_prob_eq_one_iff {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)
    (hM : Standing M) (t : ℝ) :
    M.P {ω | t ≤ M.πg + M.r ω} = 1 ↔ t ≤ M.πg + M.rl := by sorry

end SharedControl
