-- Prove2me | Theorems.Thm_ReverseLogisticsNEBS_theorem_5
-- name    : ReverseLogisticsNEBS.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:45.330489+00:00
-- url     : https://prove2.me/theorems/94bedc81-9c4b-45b7-8470-6f04fdf02fcd
-- title:
--   Theorem 5 — ordering of basestock levels (corrected: $S_{jt} \le S^R_{jt}$ only, under $c^R_j \ge 0$)
-- statement:
--   Under Assumption 1, let $c^R_j = k^R_j + k_j - h_j \ge 0$ at every location, let $1 \le t \le T$, and assume the nondegeneracy of (11)–(14) in periods $t, \dots, T$. Then at every location $j$ and for each $\omega$,
--   $$
--   S_{jt}(\omega) \le S^R_{jt}(\omega).
--   $$
--
--   The regular-order level never exceeds the reverse-order level, so the NEBS policy is a target-interval policy: below $S_{jt}$ it orders up, above $S^R_{jt}$ it returns stock, and in between it does nothing.
--
--   **Formalization Note** The levels are the extended-real levels of Theorem 4.
--
--   Differences from the source:
--   - correction: S^E_jt(ω) ≤ S_jt(ω) ≤ S^R_jt(ω) → S_jt(ω) ≤ S^R_jt(ω); reason: S^E_jt ≤ S_jt fails for nondegenerate data satisfying every assumption: N = 1, T = 1, k_1 = 1, k^E_1 = 2, k^R_1 = 1, H_1 = 1, p = 100, α = 1/2, demand ≡ 5, f_2(y) = 10|y + 10|: g = Y + 5|Y + 5| gives S = −5, u has argmin {5} so S^R = 5, and w = v has argmin {5} so S^E = 5 > S (expediting to cover the period's demand pays, a regular order arriving after the horizon does not)
--   - correction: S_jt(ω) ≤ S^R_jt(ω) with no cost condition → under c^R_j ≥ 0 at every location; reason: counterexample N = 1, T = 1, k_1 = 1, k^E_1 = 2, k^R_1 = 0.1, H_1 = 5 (c^R_1 = −3.9), p = 10, α = 1/2, demand ≡ 0, f_2(y) = 10|y − 10|: S = 10, u = γ + 3.9Y + g^+ has argmin {0}, so S^R = 0 < S; the proof (p.42) uses −c^R_N[Ŷ^R_Nt − Ȳ^R_Nt] ≥ 0, i.e. c^R ≥ 0
--   - encoding: S^E_jt := inf arg min w_jt, S^R_jt := sup arg min u_jt, S_jt := sup arg min g_jt → extended-real levels (EReal), −∞ or +∞ when the argmin is a ray; reason: the inf/sup of an argmin unbounded on one side is infinite; a real junk value would change the policy
--   - encoding: the ± notation of p.14, defined only for convex f with a finite minimizer, applied to g, u, w; the expectation in (11) → Model.Nondeg: g_js, u_js, w_js have finite minimizers and f̃_{j,s+1}(ω', Y − D_s) is integrable, in every period s ∈ [t, T]; reason: the presupposition of (11)–(14); it excludes only cases where the printed statement is undefined (paper.md item 6)
--   - reading: unit holding and backlogging costs H_j, p of unstated sign (pp.9–10) → H_j ≥ 0 and p ≥ 0 (Model.Standing); reason: unit costs; the field's standing convention, also what makes γ_t nonincreasing
--   - reading: stochastic customer demand D_t (p.7), E_ω[D_t(ω)] in γ_t (p.11) → every demand law supported on [0, ∞) with a finite mean (Model.Standing); reason: demand is a nonnegative quantity and γ_t needs E[D] < ∞ (paper.md item 3)
--   - encoding: h_j := H_j − H_{j+1} for j ∈ [1, N] with H_{N+1} undefined (p.11) → H_{N+1} := 0; reason: the only value under which (4) and (5) agree; changes no instance
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), Theorem 5, p.16; proof pp.41–45

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_comps

open MeasureTheory ProbabilityTheory

namespace ReverseLogisticsNEBS

/-- **Theorem 5** (Angelus–Özer, SSRN 3508009, Dec. 21, 2019, p.16), corrected: under
Assumption 1 and `c^R_j = k^R_j + k_j − h_j ≥ 0` at every location, at every location `j` in each
period `t ∈ [1, T]`, `S_jt(ω) ≤ S^R_jt(ω)` for each `ω`.

**Formalization Note.** The printed theorem is `S^E_jt(ω) ≤ S_jt(ω) ≤ S^R_jt(ω)` without the cost
condition. The first inequality fails for nondegenerate data satisfying every assumption of the
paper, and the second fails when `c^R_j < 0`; see the item's differences. Levels are extended reals
(`Model.SEt`, `Model.St`, `Model.SRt`). -/
theorem theorem_5 {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (M : Model N Ω) (hM : M.Standing) (hcR : M.RevRegNonneg)
    (T : ℕ) (fT : Fin N → Ω → ℝ → ℝ) (hfT : ∀ j ω, ConvexOn ℝ Set.univ (fT j ω)) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ T) (hnd : M.Nondeg T fT t) :
    ∀ j ω, M.St T fT t ω j ≤ M.SRt T fT t ω j := by sorry

end ReverseLogisticsNEBS
