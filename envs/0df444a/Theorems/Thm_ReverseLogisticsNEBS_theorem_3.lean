-- Prove2me | Theorems.Thm_ReverseLogisticsNEBS_theorem_3
-- name    : ReverseLogisticsNEBS.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:59.949947+00:00
-- url     : https://prove2.me/theorems/f95855f8-a65c-4242-8071-b962cc1ea496
-- title:
--   Theorem 3 (Preservation) — additive convexity of $\tilde f_t$ and convexity of $g, u, v, w$
-- statement:
--   Assume the terminal value is additively convex, $f_{T+1}(\omega, y) = \sum_j f_{j,T+1}(\omega, y_j)$ with every $f_{j,T+1}(\omega, \cdot)$ convex (Assumption 1), and define $g_{jt}, u_{jt}, v_{jt}, w_{jt}$ and $\tilde f_{jt} := -k^E_j y + w^+_{jt}$ backward by (11)–(14). Let $1 \le t \le T$, and assume the nondegeneracy of (11)–(14) in periods $t, \dots, T$. Then:
--
--   1. (a) for every $\omega$ and nested $y$,
--   $$
--   \tilde f_t(\omega, y) = \sum_{j=1}^N \tilde f_{jt}(\omega, y_j),
--   $$
--   that is, $\sum_j \tilde f_{jt}(\omega, y_j)$ is the attained minimum of the relaxed optimality equation (10) with continuation $\tilde f_{t+1} = \sum_j \tilde f_{j,t+1}$; and each $\tilde f_{jt}(\omega, \cdot)$ is convex;
--   2. (b) $g_{jt}(\omega, \cdot)$, $u_{jt}(\omega, \cdot)$, $v_{jt}(\omega, \cdot)$ and $w_{jt}(\omega, \cdot)$ are convex for each $j$ and $\omega$.
--
--   The value function of the relaxed problem therefore decomposes into a sum of one-dimensional convex functions given by explicit recursions, which removes the curse of dimensionality.
--
--   **Formalization Note** Since $\tilde f_{T+1} = f_{T+1}$ and (10) determines $\tilde f_t$ from $\tilde f_{t+1}$, part (a) in every period identifies $\tilde f_t$ with $\sum_j \tilde f_{jt}$.
--
--   Differences from the source:
--   - encoding: the ± notation of p.14, defined only for convex f with a finite minimizer, applied to g, u, w; the expectation in (11) → Model.Nondeg: g_js, u_js, w_js have finite minimizers and f̃_{j,s+1}(ω', Y − D_s) is integrable, in every period s ∈ [t, T]; reason: the presupposition of (11)–(14); it excludes only cases where the printed statement is undefined (paper.md item 6)
--   - encoding: f^+(x) := f(S) if x ≤ S, f(x) otherwise; f^−(y) := f(y) − f(S) if y ≤ S, 0 otherwise → f^+(x) = inf_{θ ≥ x} f(θ), f^−(y) = inf_{θ ≤ y} f(θ) − inf f; reason: equal to the paper's formulas for convex f with a finite minimizer, independent of the choice of S
--   - reading: (13) for N = 1, where the cases j = 1 and j = N coincide → v_11 = c^E_1 Y + u^+_11(ω, [Y]^−) + u^−_11(ω, Y); reason: the j = 1 case without the nonexistent u^+_2t; it is what minimizing over Y^R_1 ∈ [[Y^E_1]^−, Y^E_1] gives
--   - encoding: f̃_t(ω, ·) is additively convex with components f̃_jt → Σ_j f̃_jt(ω, y_j) is the attained minimum of (10) with continuation Σ_j f̃_{j,t+1}, at every nested y; reason: (10) defines f̃_t from f̃_{t+1}, so this identifies f̃_t; the state space is the nested states
--   - encoding: the components of f_{T+1} (any additively convex decomposition) → the given components fT; reason: components are determined up to additive constants, which shift g, u, v, w, f̃_jt by constants only
--   - reading: unit holding and backlogging costs H_j, p of unstated sign (pp.9–10) → H_j ≥ 0 and p ≥ 0 (Model.Standing); reason: unit costs; the field's standing convention, also what makes γ_t nonincreasing
--   - reading: stochastic customer demand D_t (p.7), E_ω[D_t(ω)] in γ_t (p.11) → every demand law supported on [0, ∞) with a finite mean (Model.Standing); reason: demand is a nonnegative quantity and γ_t needs E[D] < ∞ (paper.md item 3)
--   - encoding: h_j := H_j − H_{j+1} for j ∈ [1, N] with H_{N+1} undefined (p.11) → H_{N+1} := 0; reason: the only value under which (4) and (5) agree; changes no instance
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), Theorem 3, pp.14–15; proof p.40

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Sched
import Definitions.Def_ReverseLogisticsNEBS_comps

open MeasureTheory ProbabilityTheory

namespace ReverseLogisticsNEBS

/-- **Theorem 3 (Preservation)** (Angelus–Özer, SSRN 3508009, Dec. 21, 2019, pp.14–15). Let the
terminal value be additively convex, `f_{T+1}(ω, y) = Σ_j fT_j(ω, y_j)` with every `fT_j(ω, ·)`
convex (Assumption 1, p.12), and let `f̃_jt := −k^E_j y + w^+_jt` be computed backward by
(11)–(14) (`Model.comps`). In every period `t ∈ [1, T]` (with the `±` notation defined in periods
`t, …, T`):

(a) `f̃_t(ω, y) = Σ_j f̃_jt(ω, y_j)`: for every `ω` and nested `y`, `Σ_j f̃_jt(ω, y_j)` is the
attained minimum of the relaxed optimality equation (10) whose continuation is
`f̃_{t+1}(ω', y') = Σ_j f̃_{j,t+1}(ω', y'_j)`; and every `f̃_jt(ω, ·)` is convex;

(b) `g_jt(ω, ·)`, `u_jt(ω, ·)`, `v_jt(ω, ·)` and `w_jt(ω, ·)` are convex for each `j` and `ω`.

**Formalization Note.** Since `f̃_{T+1} = f_{T+1}` and (10) determines `f̃_t` from `f̃_{t+1}`, part
(a) for every period identifies `f̃_t` with `Σ_j f̃_jt`. `Model.Nondeg` is the presupposition of the
`±` notation (finite minimizers of `g, u, w`) and of (11) (finite expectations). -/
theorem theorem_3 {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (M : Model N Ω) (hM : M.Standing) (T : ℕ)
    (fT : Fin N → Ω → ℝ → ℝ) (hfT : ∀ j ω, ConvexOn ℝ Set.univ (fT j ω)) (t : ℕ) (ht : 1 ≤ t)
    (htT : t ≤ T) (hnd : M.Nondeg T fT t) :
    (∀ ω (y : Fin N → ℝ), Monotone y →
      IsLeast ((fun s => -∑ j, M.kE j * y j +
          M.stageObj t (fun ω' y' => ∑ j, M.comps T fT (t + 1) j ω' (y' j)) ω s) ''
        {s | Sched.FeasRelax y s ∧
          M.ContIntegrable t (fun ω' y' => ∑ j, M.comps T fT (t + 1) j ω' (y' j)) ω s})
        (∑ j, M.comps T fT t j ω (y j))) ∧
    (∀ j ω, ConvexOn ℝ Set.univ (M.comps T fT t j ω)) ∧
    (∀ j ω, ConvexOn ℝ Set.univ (M.gT T fT t j ω) ∧ ConvexOn ℝ Set.univ (M.uT T fT t j ω) ∧
      ConvexOn ℝ Set.univ (M.vT T fT t j ω) ∧ ConvexOn ℝ Set.univ (M.wT T fT t j ω)) := by sorry

end ReverseLogisticsNEBS
