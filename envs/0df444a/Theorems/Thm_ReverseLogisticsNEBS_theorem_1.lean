-- Prove2me | Theorems.Thm_ReverseLogisticsNEBS_theorem_1
-- name    : ReverseLogisticsNEBS.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:49.069337+00:00
-- url     : https://prove2.me/theorems/1c68ac11-6482-465b-9b3b-b556fef1c195
-- title:
--   Theorem 1 — optimal relaxed policies are unidirectional (corrected: at locations with $c^E_j, c^R_j > 0$)
-- statement:
--   In every period $t$, at every Markov state $\omega$ and installation state $x$ ($x_j \ge 0$ for $j \ge 2$), and for every continuation function $G$, **every** optimal policy $(X^E, X^R, X)$ of the relaxed problem (28) is unidirectional at every location $j$ with $c^E_j = k^E_j + k^R_j > 0$ and $c^R_j = k^R_j + k_j - h_j > 0$:
--   $$
--   \big(X^E_j = 0 \ \text{and}\ X_j = 0\big) \quad\text{or}\quad X^R_j = 0 .
--   $$
--
--   So at such a location the product flows either downstream (expedited or regular orders) or upstream (reverse orders), never both in the same period. Under the paper's cost assumptions $c^E_j > 0$ at every location except possibly $N$.
--
--   **Formalization Note** Optimality is among feasible policies of $\widetilde{\mathbb X}(x)$ with an integrable continuation; the objective is the installation form of the model's cost (4).
--
--   Differences from the source:
--   - correction: unidirectional at every location → unidirectional at every location j with c^E_j > 0 and c^R_j > 0; reason: if c^R_j < 0, holding a unit at j costs more than sending it up and ordering it back; counterexample N = 1, T = 1, k_1 = 1, k^E_1 = 2, k^R_1 = 0.1, H_1 = 5, p = 10, α = 1/2, demand ≡ 0, f_2(y) = 10|y − 10|, x_1 = 20: the unique optimum reverse-orders 20 units and regular-orders 10 (cost 52 against 91 for the best unidirectional policy); at c^R_j = 0 or c^E_N = 0 bidirectional optima arise by ties (Proposition 1's counterexample)
--   - reading: an optimal policy … is unidirectional → every optimal policy is; reason: the proof ends 'any optimal policy must be unidirectional' (p.38); paper.md item 8
--   - reading: the objective (29), p.33, with coefficient (k_jt + h_jt) on X_jt and time-indexed costs → the installation form of the model's one-period cost (4), p.11: coefficient k_j on X_j, time-independent costs; reason: (29) contradicts (4), (5) and (8), which define the model; the problem (28) is the installation form of (10)
--   - generalization: the relaxed problem's own continuation F̃_{t+1} → an arbitrary continuation function G; reason: the reductions keep the next state, so the proof never uses G; the paper's F̃_{t+1} is a special case
--   - encoding: optimal = attains the min of the objective → optimal among the feasible decisions whose expected continuation is finite (integrable); reason: a decision with an infinite expected continuation has infinite cost in the paper; Lean's Bochner integral would give it the junk value 0
--   - encoding: (1) and 𝕏̃ give no interval for X^E_N and X_N → X^E_N ≥ 0 and X_N ≥ 0; reason: numbers of units (p.8); excludes no instance of the paper
--   - reading: unit holding and backlogging costs H_j, p of unstated sign (pp.9–10) → H_j ≥ 0 and p ≥ 0 (Model.Standing); reason: unit costs; the field's standing convention, also what makes γ_t nonincreasing
--   - reading: stochastic customer demand D_t (p.7), E_ω[D_t(ω)] in γ_t (p.11) → every demand law supported on [0, ∞) with a finite mean (Model.Standing); reason: demand is a nonnegative quantity and γ_t needs E[D] < ∞ (paper.md item 3)
--   - encoding: h_j := H_j − H_{j+1} for j ∈ [1, N] with H_{N+1} undefined (p.11) → H_{N+1} := 0; reason: the only value under which (4) and (5) agree; changes no instance
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), Theorem 1, p.13; proof pp.37–38

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Inst

open MeasureTheory ProbabilityTheory

namespace ReverseLogisticsNEBS

/-- **Theorem 1** (Angelus–Özer, SSRN 3508009, Dec. 21, 2019, p.13), corrected: in every period
`t`, at every Markov state `ω` and installation state `x`, and for every continuation function
`G` of the relaxed problem, **every** optimal policy of the relaxed problem (28) is
unidirectional (`X^E_j = X_j = 0` or `X^R_j = 0`) at every location `j` with
`c^E_j = k^E_j + k^R_j > 0` and `c^R_j = k^R_j + k_j − h_j > 0`.

**Formalization Note.** The printed theorem claims unidirectionality at every location. It fails
when `c^R_j < 0` (holding a unit at `j` for a period costs more than sending it up and ordering it
back) and, by ties, when `c^E_N = 0` or `c^R_j = 0`; see the item's differences. Under the paper's
cost assumptions `c^E_j > 0` for `j ≤ N − 1`. The continuation `G` is arbitrary: the proof only
uses that the reductions of Propositions 1–2 leave the next state unchanged. -/
theorem theorem_1 {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (M : Model N Ω) (hM : M.Standing) (t : ℕ)
    (G : Ω → (Fin N → ℝ) → ℝ) (ω : Ω) (x : Fin N → ℝ) (hx : ∀ j : Fin N, 0 < j.val → 0 ≤ x j)
    (a : Inst N) (ha : M.IsOptimalInst t G ω x a) :
    ∀ j, 0 < M.cE j → 0 < M.cR j → (a.XE j = 0 ∧ a.X j = 0) ∨ a.XR j = 0 := by sorry

end ReverseLogisticsNEBS
