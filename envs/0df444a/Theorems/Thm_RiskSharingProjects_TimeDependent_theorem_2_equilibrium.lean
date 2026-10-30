-- Prove2me | Theorems.Thm_RiskSharingProjects_TimeDependent_theorem_2_equilibrium
-- name    : RiskSharingProjects.TimeDependent.theorem_2_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:25:59.014256+00:00
-- url     : https://prove2.me/theorems/12cd4843-8fc4-459f-8549-f6f93d876c59
-- title:
--   Theorem 2 (Equilibrium): the SPNE of the time-dependent-cost game in five cases
-- statement:
--   Assume Condition 2. The SPNE outcomes of the game under information symmetry are:
--
--   | Case | Condition on S | Condition on M | Optimal strategy for S | M's best response |
--   |---|---|---|---|---|
--   | 1 | $s_1<p^1_1$ | $s_0<p^1_0$ | $K$ | $K$ |
--   | 2 | $s_1>p^1_1$ | $s_0<p^1_0$ | $D$ | $K$ |
--   | 3 | ($s_1>0$) | $p^1_0<s_0<p^2_0$ | $D$ | $K$ |
--   | 4 | $s_1<p^2_1$ | $s_0>p^2_0$ | $K$ | $D$ |
--   | 5 | $s_1>p^2_1$ | $s_0>p^2_0$ | $D$ | $D$ |
--
--   In each case the set $\mathcal O^{\mathrm{sym}}$ of SPNE outcomes is exactly the single outcome in the last two columns. Case 3 is specific to time-dependent cost: a manufacturer whose saving lies between its two penalty shares delays after the supplier keeps and keeps after the supplier delays, which lets the supplier delay.
--
--   Throughout, $p^k_i$ is the penalty of the $k$-th period of project delay borne by firm $i$; firm $1$ is the supplier and firm $0$ the manufacturer.
--
--   Differences from the source:
--
--   - reading: positive saving from delay, used in the proof of Case 3 ("s1 − p^1_1" higher than "−p^1_1") → hypothesis 0 < s1 in Case 3 only; reason: the direct cost is decreasing in the task duration (p. 7); without it Case 3 fails (s1 = −1, p^1_1 = 1, p^2_1 = 2, s0 = 3/2, p^1_0 = 1, p^2_0 = 2 satisfy Condition 2 and the SPNE outcome is [K,D])
--   - encoding: "the SPNE is" the tabulated outcome → the set of pure-strategy SPNE outcomes equals the singleton of that outcome; reason: the statement includes uniqueness, which holds in each strict case
--   - generalization: the model's sign conventions (p. 7: savings s_i > 0 since the direct cost is decreasing in the task duration; penalty shares are costs), standing throughout the paper → not assumed in Cases 1, 2, 4 and 5; Case 3 carries only 0 < s1; reason: those cases follow from Condition 2 alone; specializes to the paper's model, where the conventions hold
-- source:
--   Song, Zhao, Xu, Incentives and Gaming in Collaborative Projects under Risk Sharing Partnerships, SSRN 2980139 (2019-10-14 PDF), Theorem 2, p. 12; proof Appendix p. 2 (PDF 34)

import Mathlib
import Definitions.Def_RiskSharingProjects_TimeDependent_Action
import Definitions.Def_RiskSharingProjects_TimeDependent_symmetricSPNEOutcomes
import Definitions.Def_RiskSharingProjects_TimeDependent_Condition2

namespace RiskSharingProjects.TimeDependent

/-- **Theorem 2 (Equilibrium).**
Song, Zhao, Xu, *Incentives and Gaming in Collaborative Projects under Risk Sharing
Partnerships*, SSRN 2980139 (2019-10-14 PDF), Theorem 2, p. 12 (PDF 12); proof Appendix p. 2 (PDF 34): "Under Assumption 1(b) and
Condition 2, the SPNE is,
Case 1: s1 < p^1_1, s0 < p^1_0: K, K;
Case 2: s1 > p^1_1, s0 < p^1_0: D, K;
Case 3: p^1_0 < s0 < p^2_0: D, K;
Case 4: s1 < p^2_1, s0 > p^2_0: K, D;
Case 5: s1 > p^2_1, s0 > p^2_0: D, D."

Under `Condition2`, in each case the set of SPNE outcomes of the complete-information game is
the single printed outcome (supplier's action, manufacturer's response).

**Formalization Note.** Case 3 carries `0 < s1`: the direct cost is decreasing in the task
duration (p. 7), so delaying saves `s1 > 0`, and the proof uses "s1 − p^1_1 > −p^1_1". Without it
Case 3 is false (with `s1 < 0` the SPNE outcome is `(keep, delay)`). The other cases do not need
it. Each conclusion is a set equality, so it also asserts uniqueness. Notation: `p11 p21 p10 p20` are the paper's p^1_1, p^2_1, p^1_0, p^2_0 (superscript = period
of project delay, subscript = firm; firm 1 is the supplier, firm 0 the manufacturer). -/
theorem theorem_2_equilibrium (s1 s0 p11 p21 p10 p20 : ℝ)
    (hC2 : Condition2 s1 s0 p11 p21 p10 p20) :
    (s1 < p11 → s0 < p10 →
      symmetricSPNEOutcomes s1 p11 p21 s0 p10 p20 = {(Action.keep, Action.keep)}) ∧
    (p11 < s1 → s0 < p10 →
      symmetricSPNEOutcomes s1 p11 p21 s0 p10 p20 = {(Action.delay, Action.keep)}) ∧
    (0 < s1 → p10 < s0 → s0 < p20 →
      symmetricSPNEOutcomes s1 p11 p21 s0 p10 p20 = {(Action.delay, Action.keep)}) ∧
    (s1 < p21 → p20 < s0 →
      symmetricSPNEOutcomes s1 p11 p21 s0 p10 p20 = {(Action.keep, Action.delay)}) ∧
    (p21 < s1 → p20 < s0 →
      symmetricSPNEOutcomes s1 p11 p21 s0 p10 p20 = {(Action.delay, Action.delay)}) := by sorry

end RiskSharingProjects.TimeDependent
