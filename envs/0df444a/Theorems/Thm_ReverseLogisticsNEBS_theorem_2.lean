-- Prove2me | Theorems.Thm_ReverseLogisticsNEBS_theorem_2
-- name    : ReverseLogisticsNEBS.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:14.357209+00:00
-- url     : https://prove2.me/theorems/a0de2872-da99-4d64-a9d8-3356db9ac0d7
-- title:
--   Theorem 2 — the relaxation is exact (corrected: sets of optimal schedules, under $c^R_j \ge 0$)
-- statement:
--   Let $f$ solve the optimality equations (7) of the original problem and $\tilde f$ those of the relaxed problem (10) over the horizon $T$, with $f_{T+1}(\omega, \cdot) = \tilde f_{T+1}(\omega, \cdot)$ at every nested state. Suppose $c^R_j = k^R_j + k_j - h_j \ge 0$ at every location. Then:
--
--   1. (b) $f_t(\omega, y_t) = \tilde f_t(\omega, y_t)$ for every period $t \le T + 1$, every $\omega$ and every nested $y_t$;
--   2. (a) if moreover $c^R_j > 0$ at every location $j \le N - 1$, then in every period $t \le T$, at every $\omega$ and nested $y_t$, a schedule is optimal for the original problem if and only if it is optimal for the relaxed problem.
--
--   Hence the original problem, whose feasible set has multi-dimensional boundaries, can be solved through the relaxed one.
--
--   **Formalization Note** "$f$ solves (7)" means that in every period $t \in [1, T]$ the minimum is attained and equals $f_t$; optimality is among feasible schedules with an integrable continuation.
--
--   Differences from the source:
--   - correction: (a) (Y^E_t, Y^R_t, Y_t) = (Ỹ^E_t, Ỹ^R_t, Ỹ_t) for any optimal schedules of the two problems → the sets of optimal schedules coincide, under c^R_j > 0 for j ≤ N − 1; reason: the printed (a) asserts uniqueness: N = 1, T = 1, f_2 = 0, k_1 = k^E_1 = k^R_1 = H_1 = p = 1, α = 1/2, D ~ U[0, 1], y = 2 has every (2, r, r), r ∈ [1, 2], optimal (paper.md item 7); and with c^R_1 = 0 the sets differ: N = 2, k = (1, 1), k^E = (3, 3), k^R = (1, 1), H = (3, 1), p = 1, α = 1/2, demand ≡ 0, f_3(y) = 100|y_1 − 5| + 100|y_2 − 5|, y = (5, 5): every Y^R_1 ∈ [0, 5] with Y^E = Y = (5, 5), Y^R_2 = 5 is relaxed-optimal, only Y^R_1 = 5 is feasible for (6)
--   - correction: (b) f_t = f̃_t with no cost condition → under c^R_j ≥ 0 at every location; reason: counterexample N = 2, k = (1, 1), k^E = (3, 3), k^R = (1, 1), H = (6, 3) (c^R = (−1, −1)), p = 1, α = 1/2, demand ≡ 0, T = 1, f_2(y) = 100|y_1 − 5| + 100|y_2 − 10|, y = (5, 10): the relaxed minimum of (8) is 80 (Y^R = (0, 5)), the original one is 85, since (6) forces Y^R_1 + Y^R_2 ≥ 10
--   - reading: in each period t → (b) for t ∈ [1, T + 1], (a) for t ∈ [1, T]; reason: f_t is defined for t ≤ T + 1 and decisions are taken in periods 1, …, T
--   - encoding: f_t, f̃_t defined by the minima in (7), (10) → any families f, f̃ satisfying the optimality equations with attained minima (Model.SolvesDP); reason: the recursion determines them uniquely from the terminal value; existence is Theorems 3–4
--   - encoding: optimal = attains the min of the objective → optimal among the feasible decisions whose expected continuation is finite (integrable); reason: a decision with an infinite expected continuation has infinite cost in the paper; Lean's Bochner integral would give it the junk value 0
--   - reading: unit holding and backlogging costs H_j, p of unstated sign (pp.9–10) → H_j ≥ 0 and p ≥ 0 (Model.Standing); reason: unit costs; the field's standing convention, also what makes γ_t nonincreasing
--   - reading: stochastic customer demand D_t (p.7), E_ω[D_t(ω)] in γ_t (p.11) → every demand law supported on [0, ∞) with a finite mean (Model.Standing); reason: demand is a nonnegative quantity and γ_t needs E[D] < ∞ (paper.md item 3)
--   - encoding: h_j := H_j − H_{j+1} for j ∈ [1, N] with H_{N+1} undefined (p.11) → H_{N+1} := 0; reason: the only value under which (4) and (5) agree; changes no instance
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), Theorem 2, p.13; proof pp.38–39

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Sched

open MeasureTheory ProbabilityTheory

namespace ReverseLogisticsNEBS

/-- **Theorem 2** (Angelus–Özer, SSRN 3508009, Dec. 21, 2019, p.13), corrected. Let `f` solve the
optimality equations (7) of the original problem and `f̃` those of the relaxed problem (10) over
the horizon `T`, with the same terminal value at every nested state. If
`c^R_j = k^R_j + k_j − h_j ≥ 0` at every location, then

(b) `f_t(ω, y_t) = f̃_t(ω, y_t)` in every period `t ≤ T + 1`, for all `ω` and nested `y_t`; and

(a) if moreover `c^R_j > 0` at every location `j ≤ N − 1`, then in every period `t ≤ T` a schedule
is optimal for the original problem exactly when it is optimal for the relaxed problem.

**Formalization Note.** The printed (a), `(Y^E_t, Y^R_t, Y_t) = (Ỹ^E_t, Ỹ^R_t, Ỹ_t)`, asserts that
optimal schedules are unique, which fails; the corrected (a) equates the sets of optimal
schedules. Both parts need the sign conditions on `c^R`; see the item's differences for the
counterexamples. -/
theorem theorem_2 {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (M : Model N Ω) (hM : M.Standing) (hcR : M.RevRegNonneg)
    (T : ℕ) (f fr : ℕ → Ω → (Fin N → ℝ) → ℝ) (hf : M.SolvesDP T Sched.FeasOrig f)
    (hfr : M.SolvesDP T Sched.FeasRelax fr)
    (hT : ∀ ω (y : Fin N → ℝ), Monotone y → f (T + 1) ω y = fr (T + 1) ω y) :
    (∀ t, 1 ≤ t → t ≤ T + 1 → ∀ ω (y : Fin N → ℝ), Monotone y → f t ω y = fr t ω y) ∧
    ((∀ j : Fin N, j.val + 1 < N → 0 < M.cR j) →
      ∀ t, 1 ≤ t → t ≤ T → ∀ ω (y : Fin N → ℝ), Monotone y → ∀ s : Sched N,
        M.IsOptimalDecision t (f (t + 1)) (Sched.FeasOrig y) ω s ↔
          M.IsOptimalDecision t (fr (t + 1)) (Sched.FeasRelax y) ω s) := by sorry

end ReverseLogisticsNEBS
