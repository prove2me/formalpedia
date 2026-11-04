-- Prove2me | Theorems.Thm_ReverseLogisticsNEBS_theorem_4
-- name    : ReverseLogisticsNEBS.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:26.531076+00:00
-- url     : https://prove2.me/theorems/b457e658-f2c0-4d7b-9b72-838037751b35
-- title:
--   Theorem 4 (Optimality) — the NEBS schedule (15)–(17) is optimal (corrected: for (7) under $c^R_j \ge 0$)
-- statement:
--   Under Assumption 1, with $g_{jt}, u_{jt}, v_{jt}, w_{jt}$ as in Theorem 3, let
--   $$
--   S^E_{jt}(\omega) := \inf\arg\min_Y w_{jt}(\omega, Y),\qquad S^R_{jt}(\omega) := \sup\arg\min_Y u_{jt}(\omega, Y),\qquad S_{jt}(\omega) := \sup\arg\min_Y g_{jt}(\omega, Y).
--   $$
--   Let $1 \le t \le T$, assume the nondegeneracy of (11)–(14) in periods $t, \dots, T$ and that $\arg\min g_{Nt}(\omega, \cdot)$ is bounded above. Then for every $\omega$ and nested $y_t$, the schedule $(\widehat Y^E_t, \widehat Y^R_t, \widehat Y_t)$ of (15)–(17) is real-valued and
--
--   1. it is an optimal decision of the relaxed problem (10) with continuation $\tilde f_{t+1} = \sum_j \tilde f_{j,t+1}$;
--   2. if $c^R_j = k^R_j + k_j - h_j \ge 0$ at every location, it is also an optimal decision of the original problem (7) with the same continuation (which is $f_{t+1}$ by Theorems 2–3).
--
--   The optimal policy is thus a **nested echelon basestock (NEBS)** policy: each flow is a basestock rule nested inside the previous one.
--
--   **Formalization Note** The levels are extended reals; (15)–(17) are evaluated in `EReal` with the state coerced, and the conclusion states that the result is the coercion of a real schedule.
--
--   Differences from the source:
--   - correction: the NEBS schedule is the optimal policy for the reverse logistics problem, with no cost condition → optimal for the relaxed problem (10) always, and for the original problem (7) when c^R_j ≥ 0 at every location; reason: with c^R_j < 0 the NEBS schedule can be infeasible for (6): N = 2, k = (1, 1), k^E = (3, 3), k^R = (1, 1), H = (6, 3), p = 1, α = 1/2, demand ≡ 0, T = 1, f_2(y) = 100|y_1 − 5| + 100|y_2 − 10|, y = (5, 10): (15)–(17) give Y^E = (5, 10), Y^R = (0, 5), Y = (5, 10), the unique relaxed optimum, which violates Y_1 ≤ Y^R_2 − (Y^E_1 − Y^R_1)
--   - encoding: S^E_jt := inf arg min w_jt, S^R_jt := sup arg min u_jt, S_jt := sup arg min g_jt → extended-real levels (EReal), −∞ or +∞ when the argmin is a ray; reason: the inf/sup of an argmin unbounded on one side is infinite; a real junk value would change the policy
--   - encoding: the ± notation of p.14, defined only for convex f with a finite minimizer, applied to g, u, w; the expectation in (11) → Model.Nondeg: g_js, u_js, w_js have finite minimizers and f̃_{j,s+1}(ω', Y − D_s) is integrable, in every period s ∈ [t, T]; reason: the presupposition of (11)–(14); it excludes only cases where the printed statement is undefined (paper.md item 6)
--   - encoding: Ŷ_Nt = max[Ŷ^R_Nt, S_Nt] with S_Nt = sup arg min g_Nt → arg min g_Nt(ω, ·) bounded above (hypothesis); reason: otherwise S_Nt = +∞ and (17) is undefined at j = N
--   - reading: the optimal post-expedite / post-reverse / post-regular schedules → the schedule (15)–(17) is an optimal decision (attains the minimum of (10), resp. (7)); reason: optimal schedules need not be unique; the theorem identifies one optimal decision
--   - encoding: optimal = attains the min of the objective → optimal among the feasible decisions whose expected continuation is finite (integrable); reason: a decision with an infinite expected continuation has infinite cost in the paper; Lean's Bochner integral would give it the junk value 0
--   - reading: unit holding and backlogging costs H_j, p of unstated sign (pp.9–10) → H_j ≥ 0 and p ≥ 0 (Model.Standing); reason: unit costs; the field's standing convention, also what makes γ_t nonincreasing
--   - reading: stochastic customer demand D_t (p.7), E_ω[D_t(ω)] in γ_t (p.11) → every demand law supported on [0, ∞) with a finite mean (Model.Standing); reason: demand is a nonnegative quantity and γ_t needs E[D] < ∞ (paper.md item 3)
--   - encoding: h_j := H_j − H_{j+1} for j ∈ [1, N] with H_{N+1} undefined (p.11) → H_{N+1} := 0; reason: the only value under which (4) and (5) agree; changes no instance
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), Theorem 4, (15)–(17), p.15; proof p.41

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Sched
import Definitions.Def_ReverseLogisticsNEBS_comps
import Definitions.Def_ReverseLogisticsNEBS_nebsE

open MeasureTheory ProbabilityTheory

namespace ReverseLogisticsNEBS

/-- **Theorem 4 (Optimality)** (Angelus–Özer, SSRN 3508009, Dec. 21, 2019, p.15). Under
Assumption 1 and with `g_jt, u_jt, v_jt, w_jt` of Theorem 3, let
`S^E_jt(ω) := inf arg min_Y w_jt(ω, Y)`, `S^R_jt(ω) := sup arg min_Y u_jt(ω, Y)` and
`S_jt(ω) := sup arg min_Y g_jt(ω, Y)`. In every period `t ∈ [1, T]`, at every `ω` and nested
`y_t`, the schedule `(Ŷ^E_t, Ŷ^R_t, Ŷ_t)` of (15)–(17) is real-valued and is an optimal decision of
the relaxed problem (10), with continuation `f̃_{t+1} = Σ_j f̃_{j,t+1}`; and, when
`c^R_j = k^R_j + k_j − h_j ≥ 0` at every location, it is also an optimal decision of the original
problem (7) with the same continuation (which is `f_{t+1}` by Theorems 2–3).

**Formalization Note.** The levels are extended reals (`inf`/`sup` of an argmin may be `∓∞`);
(15)–(17) are evaluated in `EReal` with the state coerced, and the conclusion asserts that the
result is the coercion of a real schedule. `Model.Nondeg` is the presupposition of the `±`
notation and of (11); the condition that `arg min g_Nt` is bounded above is the presupposition of
(17) at `j = N` (`Ŷ_Nt = max[Ŷ^R_Nt, S_Nt]` is `+∞` otherwise). -/
theorem theorem_4 {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (M : Model N Ω) (hM : M.Standing) (T : ℕ)
    (fT : Fin N → Ω → ℝ → ℝ) (hfT : ∀ j ω, ConvexOn ℝ Set.univ (fT j ω)) (t : ℕ) (ht : 1 ≤ t)
    (htT : t ≤ T) (hnd : M.Nondeg T fT t)
    (hgN : ∀ j : Fin N, j.val + 1 = N → ∀ ω, BddAbove (argminSet (M.gT T fT t j ω))) :
    ∀ ω (y : Fin N → ℝ), Monotone y → ∃ s : Sched N,
      (∀ j, (s.YE j : EReal) = nebsE (M.SEt T fT t ω) (fun i => (y i : EReal)) j) ∧
      (∀ j, (s.YR j : EReal) =
        nebsR (M.SEt T fT t ω) (M.SRt T fT t ω) (fun i => (y i : EReal)) j) ∧
      (∀ j, (s.Y j : EReal) =
        nebsY (M.SEt T fT t ω) (M.SRt T fT t ω) (M.St T fT t ω) (fun i => (y i : EReal)) j) ∧
      M.IsOptimalDecision t (fun ω' y' => ∑ j, M.comps T fT (t + 1) j ω' (y' j))
        (Sched.FeasRelax y) ω s ∧
      (M.RevRegNonneg →
        M.IsOptimalDecision t (fun ω' y' => ∑ j, M.comps T fT (t + 1) j ω' (y' j))
          (Sched.FeasOrig y) ω s) := by sorry

end ReverseLogisticsNEBS
