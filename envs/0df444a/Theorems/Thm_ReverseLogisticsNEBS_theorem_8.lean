-- Prove2me | Theorems.Thm_ReverseLogisticsNEBS_theorem_8
-- name    : ReverseLogisticsNEBS.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:17.176303+00:00
-- url     : https://prove2.me/theorems/6bea42f0-ec32-4b8e-9d39-091b92d5c7ab
-- title:
--   Theorem 8 — without demand variability, no reverse orders after period $N-j+1$
-- statement:
--   Consider the model **without Markov modulation** (a single Markov state, so demands are i.i.d. across periods, Assumption 2). Let $S^E_j \le S_j \le S^R_j$ be the basestock levels of a stationary nested echelon basestock policy that is optimal for the infinite-horizon problem (18). Start from a nested echelon state $y_1$ in period $1$ and follow this policy, the state evolving by $y_{t+1} = \widehat Y_t - d_t$ under any nonnegative demands $d_1, d_2, \dots$. Then:
--
--   1. (a) if $y_{j1} \le S^R_j$ at every location $j$, the policy never places a reverse order: $X^R_{it} = \widehat Y^E_{it} - \widehat Y^R_{it} = 0$ for every location $i$ and every period $t \ge 1$;
--   2. (b) if $y_{j1} > S^R_j$ for some location, and $j$ is the smallest such location, then $X^R_{it} = 0$ for every location $i$ and every period $t \ge N - j + 2$, i.e. after period $N - j + 1$.
--
--   However volatile demand is within a period, without variability across periods reverse logistics is used at most during the first $N$ periods and creates no value afterwards.
--
--   **Formalization Note** Locations are indexed from $0$ in Lean, so the paper's location $j$ is index $j-1$ and "after period $N - j + 1$" becomes $t \ge N - (j-1) + 1$.
--
--   Differences from the source:
--   - reading: the basestock levels of a stationary, optimal nested echelon basestock policy given in Theorem 7 → real levels with S^E_j ≤ S_j ≤ S^R_j whose stationary NEBS policy satisfies IsOptimalInfinite; reason: the ordering is part of what Theorems 6–7 deliver (Theorem 6(2), p.17; proof of Theorem 7, p.45); the optimality hypothesis is kept although the proof (pp.46–49) does not use it (paper.md item 1)
--   - generalization: it is never optimal to reverse order (along the random demand process) → the policy's reverse orders vanish along every nonnegative demand path; reason: pathwise for every demand sequence implies the almost-sure statement for the random demands (paper.md item 2)
--   - reading: the infinite-horizon problem (18) → IsOptimalInfinite: costs through (5)/(8) with y_τ = Y_{τ−1} − D_{τ−1}, Markov policies, comparison among policies with finite expectations and a convergent cost; reason: (18) writes D_τ in the −k^E_j term and (p + H_1)(D − Y^R_1)^+ instead of γ (paper.md item 5)
--   - encoding: in the absence of Markov-modulation; Assumption 2 → a single Markov state (Unit) and a time-homogeneous kernel (Model.Stationary); reason: one state means demands are i.i.d. across periods; same instances
--   - encoding: after period N − j + 1 (1-based location j) → t ≥ N − j.val + 1 with 0-based index j.val = j − 1; reason: index convention (paper.md item 11)
--   - reading: unit holding and backlogging costs H_j, p of unstated sign (pp.9–10) → H_j ≥ 0 and p ≥ 0 (Model.Standing); reason: unit costs; the field's standing convention, also what makes γ_t nonincreasing
--   - reading: stochastic customer demand D_t (p.7), E_ω[D_t(ω)] in γ_t (p.11) → every demand law supported on [0, ∞) with a finite mean (Model.Standing); reason: demand is a nonnegative quantity and γ_t needs E[D] < ∞ (paper.md item 3)
--   - encoding: h_j := H_j − H_{j+1} for j ∈ [1, N] with H_{N+1} undefined (p.11) → H_{N+1} := 0; reason: the only value under which (4) and (5) agree; changes no instance
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), Theorem 8, p.17; proof pp.46–49

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_nebsE
import Definitions.Def_ReverseLogisticsNEBS_IsOptimalInfinite

open MeasureTheory ProbabilityTheory

namespace ReverseLogisticsNEBS

/-- **Theorem 8** (Angelus–Özer, *When Variability Trumps Volatility*, SSRN 3508009,
Dec. 21, 2019, p.17). In the absence of Markov modulation (one Markov state, demands IID), let
`S^E_j ≤ S_j ≤ S^R_j` be the basestock levels of a stationary nested echelon basestock policy that
is optimal for the infinite-horizon problem (18). Start from a nested echelon state `y_1` in
period `1` and follow the policy under any nonnegative demands `d_1, d_2, …`. Then

(a) if `y_j1 ≤ S^R_j` at every location `j`, the policy places no reverse order at any location in
any period; and

(b) if `j` is the smallest location with `y_j1 > S^R_j`, the policy places no reverse order at any
location in any period after period `N − j + 1`.

**Formalization Note.** Locations are `Fin N`: index `j` is location `j + 1`, so "after period
`N − (j + 1) + 1`" is `t ≥ N − j + 1` (periods `1`-based). The single Markov state is `Unit`;
`Model.Stationary` is Assumption 2. The ordering `S^E_j ≤ S_j ≤ S^R_j` is part of what "the
basestock levels of a stationary, optimal NEBS policy given in Theorem 7" provides (Theorem 6(2),
p.17). The conclusion is pathwise, for every nonnegative demand sequence; it implies the almost
sure statement. -/
theorem theorem_8 {N : ℕ} (M : Model N Unit) (hM : M.Standing) (hstat : M.Stationary)
    (SE SR S : Fin N → ℝ) (hord : ∀ j, SE j ≤ S j ∧ S j ≤ SR j)
    (hopt : M.IsOptimalInfinite (fun _ => SE) (fun _ => SR) (fun _ => S))
    (y₁ : Fin N → ℝ) (hy₁ : Monotone y₁) (d : ℕ → ℝ) (hd : ∀ t, 0 ≤ d t) :
    ((∀ j, y₁ j ≤ SR j) → ∀ t, 1 ≤ t → ∀ i, reverseOrder SE SR S y₁ d t i = 0) ∧
    (∀ j : Fin N, SR j < y₁ j → (∀ i : Fin N, i < j → y₁ i ≤ SR i) →
      ∀ t, N - j.val + 1 ≤ t → ∀ i, reverseOrder SE SR S y₁ d t i = 0) := by sorry

end ReverseLogisticsNEBS
