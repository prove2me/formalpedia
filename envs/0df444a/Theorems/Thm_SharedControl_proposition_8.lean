-- Prove2me | Theorems.Thm_SharedControl_proposition_8
-- name    : SharedControl.proposition_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:09:49.404821+00:00
-- url     : https://prove2.me/theorems/ba66c77a-da51-48ee-a6f2-3c0ba07bd797
-- title:
--   Proposition 8 — with limits on transfers, $S$ increases in $z$ and $\tilde U$ does not change
-- statement:
--   Assume the standing assumptions, and suppose that undivided control is associated with limits on transfers. Let $z \in [0,1]$ be the probability that the stakeholder observes the redistribution $r$, let
--
--   $$
--   S(z) = q\bigl[z + (1 - z)\Pr[m_g \ge t_s]\bigr]2\pi_g
--   \qquad\text{and}\qquad
--   \tilde U(z) = 2\bigl[q\pi_g + (1 - q)\Pr[m_b \ge 0]\pi_b\bigr]
--   $$
--
--   be the joint expected surpluses of shared control, equation (3), and of undivided control with limits on transfers, equation (7). Then, as the stakeholder becomes better informed:
--
--   1. the benefit of shared control increases: $S$ is nondecreasing on $[0,1]$;
--   2. the increase is strict exactly when some good proposals are blocked: $S$ is strictly increasing on $[0,1]$ if and only if
--   $$
--   q > 0 \quad\text{and}\quad \bar r - r_l > 2\pi_g ;
--   $$
--   3. the benefit of undivided control does not change: $\tilde U(z) = \tilde U(z')$ for all $z, z'$;
--   4. consequently $\tilde U - S$ is nonincreasing on $[0,1]$, so shared control becomes relatively more attractive.
--
--   This is the paper's asymmetry result: with limits on transfers there is no ex post bargaining under undivided control, so only shared control gains from a better-informed stakeholder, in contrast to the case without limits on transfers.
--
--   **Formalization Note** "Increase" is read weakly: with $r$ uniform on $[0,1]$, $\pi_g = 1$, $\pi_b = -1$, $q = 1/2$, one has $t_s = 0$, $\Pr[m_g \ge t_s] = 1$ and $S$ constant, so a strict increase can fail; clause 2 gives the exact condition for it. $t_s$ is the least transfer satisfying Inequality (1) of the paper, defined from the model.
--
--   Differences from the source:
--   - reading: a corresponding increase in the benefit of shared control as z increases → S is monotone (nondecreasing) on [0, 1]; reason: the strict reading is false: r uniform on [0, 1], πg = 1, πb = −1, q = 1/2 give ts = 0, Ps = 1 and S constant; clause 2 states when the increase is strict
--   - reading: the benefit of shared control and the benefit of undivided control, the latter associated with limits on transfers → the joint expected surpluses S of (3) and Ũ of (7); reason: (3) and (7) are the paper's surpluses of the two control structures, (7) being the one with limits on transfers
--   - generalization: (not stated) → S is strictly increasing on [0, 1] iff q > 0 and 2πg < r̄ − rl; reason: the exact strictness condition, from Proposition 1; an added clause, so the statement implies the source's
--   - generalization: (not stated in Proposition 8; the abstract's consequence that shared control is then more likely) → Ũ − S is antitone on [0, 1]; reason: an added clause that follows from clauses 1 and 3
--   - encoding: Ũ, a number not depending on z → Ũ a function of z that ignores its argument, constant for all real z, z'; reason: makes no change as z increases a statement about a function of z; same value (7)
--   - encoding: E[sg + t | mg ≥ t] in Inequality (1) → the integral of πg − r + t against the conditional measure P[|{mg ≥ t}], with Pr[mg ≥ t] > 0 required for t to satisfy (1); reason: a conditional expectation given a null event is undefined (Lean's cond returns the zero measure there); the least transfer satisfying (1) is unchanged
--   - generalization: r has a continuous distribution with support on [rl, rh], rl the minimum of the support → the law of r is atomless, r ∈ [rl, rh] almost surely, and every set {r < rl + ε}, {rh − ε < r} (ε > 0) has positive probability; reason: these three properties follow from supp(law r) = [rl, rh]; gaps inside (rl, rh) are also allowed, and no density is assumed, so the source's models are a special case
-- source:
--   Meyersson Milgrom, Milgrom, Singh, When Should Control Be Shared?, Management Science (2023), doi:10.1287/mnsc.2022.4356, Proposition 8, p.8

import Mathlib
import Definitions.Def_SharedControl_Model
import Definitions.Def_SharedControl_Standing
import Definitions.Def_SharedControl_Feasible
import Definitions.Def_SharedControl_ts
import Definitions.Def_SharedControl_rbar
import Definitions.Def_SharedControl_Ps
import Definitions.Def_SharedControl_S
import Definitions.Def_SharedControl_Utilde

namespace SharedControl

/-- Meyersson Milgrom, Milgrom, Singh, *When Should Control Be Shared?*, Management Science
(2023), doi:10.1287/mnsc.2022.4356, Proposition 8, p.8 (PDF p.9): "Suppose undivided control is
associated with limits on transfers. As the stakeholder becomes better informed (z increases),
there is a corresponding increase in the benefit of shared control and no change in the benefit
of undivided control."

With `S` the surplus (3) of shared control and `Ũ` the surplus (7) of undivided control with
limits on transfers, as functions of the probability `z ∈ [0, 1]` that the stakeholder observes
`r`:
1. `S` is monotone (nondecreasing) on `[0, 1]`;
2. `S` is strictly increasing on `[0, 1]` iff `q > 0` and `r̄ − rl > 2πg`;
3. `Ũ` does not depend on `z`;
4. `Ũ − S` is antitone on `[0, 1]` (shared control becomes relatively more attractive).

**Formalization Note.** "Increase" is read as weak monotonicity (clause 1): with `r` uniform on
`[0, 1]`, `πg = 1`, `πb = −1`, `q = 1/2` one has `ts = 0`, `Ps = 1` and `S` constant, so the strict
reading is false; clause 2 states exactly when the increase is strict. "Limits on transfers" is
expressed by using `Ũ` of (7), which takes `z` as an unused argument. -/
theorem proposition_8 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : Standing M) :
    MonotoneOn (S M) (Set.Icc 0 1) ∧
      (StrictMonoOn (S M) (Set.Icc 0 1) ↔ (0 < M.q ∧ 2 * M.πg < rbar M - M.rl)) ∧
      (∀ z z' : ℝ, Utilde M z = Utilde M z') ∧
      AntitoneOn (fun z => Utilde M z - S M z) (Set.Icc 0 1) := by sorry

end SharedControl
