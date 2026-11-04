-- Prove2me | Theorems.Thm_ReverseLogisticsNEBS_proposition_2
-- name    : ReverseLogisticsNEBS.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:43.531742+00:00
-- url     : https://prove2.me/theorems/9a2aa8de-bd36-44a9-b52d-4004625ea72e
-- title:
--   Proposition 2 — the unidirectional reduction (corrected: (f)–(g) need $c^R_j \ge 0$)
-- statement:
--   Fix $t$, $\omega$, an installation state $x$ ($x_j \ge 0$ for $j \ge 2$) and a continuation $G$. Let $(X^E, X^R, X)$ be feasible for $x$ (in $\mathbb X(x)$ or in $\widetilde{\mathbb X}(x)$), let $(\widehat X^E, \widehat X^R, \widehat X)$ be its semi-unidirectional reduction (Proposition 1), and define
--   $$
--   \widetilde X^E_j = \widehat X^E_j,\qquad \widetilde X^R_j = [\widehat X^R_j - \widehat X_j]^+,\qquad \widetilde X_j = [\widehat X_j - \widehat X^R_j]^+ .
--   $$
--   Then:
--
--   1. $\widetilde X^E_j, \widetilde X^R_j, \widetilde X_j \ge 0$;
--   2. at each $j$, $\widetilde X^E_j = \widetilde X_j = 0$ or $\widetilde X^R_j = 0$;
--   3. $\widetilde X^R_j \le \widehat X^R_j \le X^R_j$ and $\widetilde X_j \le \widehat X_j \le X_j$;
--   4. $(\widetilde X^E, \widetilde X^R, \widetilde X)$ is feasible in the same set;
--   5. it leads to the same next state as $(\widehat X^E, \widehat X^R, \widehat X)$, for every demand;
--   6. if $c^R_j = k^R_j + k_j - h_j \ge 0$ at every location, then $\widetilde V_t(\widetilde X) \le \widetilde V_t(\widehat X)$;
--   7. if moreover $\widehat X^R_j > 0$ and $\widehat X_j > 0$ at some location with $c^R_j > 0$, the inequality is strict.
--
--   Together with Proposition 1 this shows that any policy can be replaced by a unidirectional one with the same next state and no larger cost.
--
--   **Formalization Note** $\widetilde V_t$ is the installation form of the model's one-period cost (4). Cancelling $m$ units of simultaneous reverse and regular orders at $j$ changes it by $-c^R_j m$ plus a nonpositive change of $\gamma_t$.
--
--   Differences from the source:
--   - reading: the objective (29), p.33, with coefficient (k_jt + h_jt) on X_jt and time-indexed costs → the installation form of the model's one-period cost (4), p.11: coefficient k_j on X_j, time-independent costs; reason: (29) contradicts (4), (5) and (8), which define the model; under (29) the cancellation in (g) would save (k_j + k^R_j)m instead of c^R_j m
--   - generalization: a policy feasible for x_t, and (d) ∈ 𝕏(x_t) (the proof works with 𝕏̃(x_t) of p.33) → for each of 𝕏(x) of (1) and 𝕏̃(x) of p.33: feasible for it implies the reduction is feasible for it; reason: the page names 𝕏 while the appendix and its proofs work with 𝕏̃; the statement holds for both, so it specializes to either reading
--   - generalization: the continuation F̃_{t+1} of (29) → an arbitrary continuation function G; reason: the reductions leave the next state unchanged, so the continuation terms coincide; the paper's F̃_{t+1} is a special case
--   - encoding: (1) and 𝕏̃ give no interval for X^E_N and X_N → X^E_N ≥ 0 and X_N ≥ 0; reason: numbers of units (p.8); excludes no instance of the paper
--   - correction: (f) Ṽ_t(X̃) ≤ Ṽ_t(X̂) and (g) strict if X̂ is not unidirectional, with no cost condition → (f) under c^R_j ≥ 0 at every j; (g) under c^R_j ≥ 0 at every j and X̂^R_j, X̂_j > 0 at some j with c^R_j > 0; reason: with the model's cost (4) the cancellation changes the cost by −c^R_j·min(X̂^R_j, X̂_j); counterexample N = 1, k_1 = 1, k^E_1 = 2, k^R_1 = 0.1, H_1 = 5 (c^R_1 = −3.9), p = 10, α = 1/2, demand ≡ 0, x_1 = 20, (X^E, X^R, X) = (0, 20, 10): X̂ = X, X̃ = (0, 10, 0), same next state, γ(0) = γ(10) = 0, and Ṽ_t(X̃) − Ṽ_t(X̂) = −49 − (−88) = 39 > 0
--   - reading: unit holding and backlogging costs H_j, p of unstated sign (pp.9–10) → H_j ≥ 0 and p ≥ 0 (Model.Standing); reason: unit costs; the field's standing convention, also what makes γ_t nonincreasing
--   - reading: stochastic customer demand D_t (p.7), E_ω[D_t(ω)] in γ_t (p.11) → every demand law supported on [0, ∞) with a finite mean (Model.Standing); reason: demand is a nonnegative quantity and γ_t needs E[D] < ∞ (paper.md item 3)
--   - encoding: h_j := H_j − H_{j+1} for j ∈ [1, N] with H_{N+1} undefined (p.11) → H_{N+1} := 0; reason: the only value under which (4) and (5) agree; changes no instance
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), Proposition 2, p.35

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Inst

open MeasureTheory ProbabilityTheory

namespace ReverseLogisticsNEBS

/-- **Proposition 2** (Angelus–Özer, SSRN 3508009, Dec. 21, 2019, p.35): let `â` be the
semi-unidirectional reduction of a feasible policy `a` and `ã` the policy
`X̃^E_j = X̂^E_j`, `X̃^R_j = [X̂^R_j − X̂_j]^+`, `X̃_j = [X̂_j − X̂^R_j]^+`. Then (a) `ã ≥ 0`;
(b) `ã` is unidirectional; (c) `X̃^R_j ≤ X̂^R_j ≤ X^R_j` and `X̃_j ≤ X̂_j ≤ X_j`; (d) `ã` is
feasible; (e) `ã` and `â` yield the same next state; and, when `c^R_j = k^R_j + k_j − h_j ≥ 0` at
every location, (f) `Ṽ_t(ã) ≤ Ṽ_t(â)` and (g) `Ṽ_t(ã) < Ṽ_t(â)` if `â` regular- and
reverse-orders at some location with `c^R_j > 0`.

**Formalization Note.** `relaxed` selects `𝕏(x)` of (1) or `𝕏̃(x)` of p.33; the statement holds
for each. The objective is the installation form of the one-period cost (4) (coefficient `k_j` of
`X_j`), not the `(k_jt + h_jt)` printed in (29); with it, cancelling `m` units of simultaneous
regular and reverse orders at `j` changes the cost by `−c^R_j m` plus a nonpositive change of
`γ_t`, so (f) and (g) need the sign conditions stated. -/
theorem proposition_2 {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (M : Model N Ω) (hM : M.Standing) (t : ℕ)
    (G : Ω → (Fin N → ℝ) → ℝ) (ω : Ω) (x : Fin N → ℝ) (hx : ∀ j : Fin N, 0 < j.val → 0 ≤ x j)
    (relaxed : Bool) (a : Inst N) (ha : Inst.Feas relaxed x a) :
    (∀ j, 0 ≤ a.semiReduce.uniReduce.XE j ∧ 0 ≤ a.semiReduce.uniReduce.XR j ∧
      0 ≤ a.semiReduce.uniReduce.X j) ∧
    (∀ j, (a.semiReduce.uniReduce.XE j = 0 ∧ a.semiReduce.uniReduce.X j = 0) ∨
      a.semiReduce.uniReduce.XR j = 0) ∧
    (∀ j, a.semiReduce.uniReduce.XR j ≤ a.semiReduce.XR j ∧ a.semiReduce.XR j ≤ a.XR j ∧
      a.semiReduce.uniReduce.X j ≤ a.semiReduce.X j ∧ a.semiReduce.X j ≤ a.X j) ∧
    Inst.Feas relaxed x a.semiReduce.uniReduce ∧
    (∀ d, Inst.next x a.semiReduce.uniReduce d = Inst.next x a.semiReduce d) ∧
    (M.RevRegNonneg →
      M.instObj t G ω x a.semiReduce.uniReduce ≤ M.instObj t G ω x a.semiReduce) ∧
    (M.RevRegNonneg → (∃ j, 0 < a.semiReduce.XR j ∧ 0 < a.semiReduce.X j ∧ 0 < M.cR j) →
      M.instObj t G ω x a.semiReduce.uniReduce < M.instObj t G ω x a.semiReduce) := by sorry

end ReverseLogisticsNEBS
