-- Prove2me | Theorems.Thm_ReverseLogisticsNEBS_proposition_1
-- name    : ReverseLogisticsNEBS.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:34.723205+00:00
-- url     : https://prove2.me/theorems/8d435f04-df14-4be9-ae1f-c8c4080afbe9
-- title:
--   Proposition 1 — the semi-unidirectional reduction (corrected: (g) needs $k^E_j+k^R_j>0$)
-- statement:
--   Fix a period $t$, a Markov state $\omega$, an installation state $x$ ($x_j \ge 0$ for $j \ge 2$) and a continuation function $G$. Let $(X^E, X^R, X)$ be feasible for $x$, in either $\mathbb X(x)$ or $\widetilde{\mathbb X}(x)$, and let
--   $$
--   \widehat X^E_j = [X^E_j - X^R_j]^+,\qquad \widehat X^R_j = [X^R_j - X^E_j]^+,\qquad \widehat X_j = X_j .
--   $$
--   Then:
--
--   1. $\widehat X^E_j, \widehat X^R_j, \widehat X_j \ge 0$ for all $j$;
--   2. $\widehat X^E_j = 0$ or $\widehat X^R_j = 0$ for all $j$;
--   3. $\widehat X^E_j \le X^E_j$ and $\widehat X^R_j \le X^R_j$ for all $j$;
--   4. $(\widehat X^E, \widehat X^R, \widehat X)$ is feasible in the same set;
--   5. both policies lead to the same inventory state in period $t+1$, for every demand;
--   6. $\widetilde V_t(\omega, x, \widehat X^E, \widehat X^R, \widehat X) \le \widetilde V_t(\omega, x, X^E, X^R, X)$;
--   7. the inequality is strict if $X^E_j > 0$ and $X^R_j > 0$ at some location $j$ with $k^E_j + k^R_j > 0$.
--
--   Cancelling simultaneous expedited and reverse orders at a location never raises the cost; it is the first step in proving that optimal policies are unidirectional (Theorem 1).
--
--   **Formalization Note** $\widetilde V_t$ is the installation form of the model's one-period cost (4) (see the definition `Inst`).
--
--   Differences from the source:
--   - reading: the objective (29), p.33, with coefficient (k_jt + h_jt) on X_jt and time-indexed costs → the installation form of the model's one-period cost (4), p.11: coefficient k_j on X_j, time-independent costs; reason: (29) contradicts (4), (5) and (8), which define the model (the echelon cost (5) follows from (4), not from (29)); the model's costs are constant in time (p.10)
--   - generalization: a policy feasible for x_t, and (d) ∈ 𝕏(x_t) (the proof works with 𝕏̃(x_t) of p.33) → for each of 𝕏(x) of (1) and 𝕏̃(x) of p.33: feasible for it implies the reduction is feasible for it; reason: the page names 𝕏 while the appendix and its proofs work with 𝕏̃; the statement holds for both, so it specializes to either reading
--   - generalization: the continuation F̃_{t+1} of (29) → an arbitrary continuation function G; reason: the reductions leave the next state unchanged, so the continuation terms coincide; the paper's F̃_{t+1} is a special case
--   - encoding: (1) and 𝕏̃ give no interval for X^E_N and X_N → X^E_N ≥ 0 and X_N ≥ 0; reason: numbers of units (p.8); excludes no instance of the paper
--   - correction: (g) strict whenever the policy is not semi-unidirectional → strict when X^E_j > 0 and X^R_j > 0 at some j with k^E_j + k^R_j > 0; reason: at the allowed boundary k^E_N = k_N = −k^R_N the cancellation saves (k^E_N + k^R_N)·min(X^E_N, X^R_N) = 0; counterexample N = 1, k_1 = k^E_1 = 1, k^R_1 = −1, H_1 = 1, any p, α, demand law, x_1 = 0, (X^E_1, X^R_1, X_1) = (1, 1, 0): feasible, not semi-unidirectional, and both objectives are equal (same γ argument, same next state); k^E_j + k^R_j > 0 holds automatically at j ≤ N − 1
--   - reading: unit holding and backlogging costs H_j, p of unstated sign (pp.9–10) → H_j ≥ 0 and p ≥ 0 (Model.Standing); reason: unit costs; the field's standing convention, also what makes γ_t nonincreasing
--   - reading: stochastic customer demand D_t (p.7), E_ω[D_t(ω)] in γ_t (p.11) → every demand law supported on [0, ∞) with a finite mean (Model.Standing); reason: demand is a nonnegative quantity and γ_t needs E[D] < ∞ (paper.md item 3)
--   - encoding: h_j := H_j − H_{j+1} for j ∈ [1, N] with H_{N+1} undefined (p.11) → H_{N+1} := 0; reason: the only value under which (4) and (5) agree; changes no instance
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), Proposition 1, p.33

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Inst

open MeasureTheory ProbabilityTheory

namespace ReverseLogisticsNEBS

/-- **Proposition 1** (Angelus–Özer, *When Variability Trumps Volatility*, SSRN 3508009,
Dec. 21, 2019, p.33): the semi-unidirectional reduction
`X̂^E_j = [X^E_j − X^R_j]^+`, `X̂^R_j = [X^R_j − X^E_j]^+`, `X̂_j = X_j` of a feasible policy
(a) is nonnegative, (b) is semi-unidirectional, (c) reduces the expedited and reverse orders,
(d) is feasible, (e) yields the same next inventory state for every demand, (f) has an
installation objective (29) at most that of the original policy, and (g) a strictly smaller one
when the original policy expedites and reverse-orders at some location `j` with
`k^E_j + k^R_j > 0`.

**Formalization Note.** `relaxed` selects the feasible set: `𝕏(x)` of (1) or `𝕏̃(x)` of p.33
(the proposition and its proof use both names); the statement holds for each. The state `x` is an
installation state (`x_j ≥ 0` for `j ≥ 2`; `x_1`, the net inventory, may be negative). The
objective uses the one-period cost (4); see `Model.instObj`. In (g) the printed condition is "not
semi-unidirectional"; it is required here at a location with `k^E_j + k^R_j > 0`, which is
automatic at locations `1, …, N − 1` and fails only at the boundary `k^E_N = k_N = −k^R_N`. -/
theorem proposition_1 {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (M : Model N Ω) (hM : M.Standing) (t : ℕ)
    (G : Ω → (Fin N → ℝ) → ℝ) (ω : Ω) (x : Fin N → ℝ) (hx : ∀ j : Fin N, 0 < j.val → 0 ≤ x j)
    (relaxed : Bool) (a : Inst N) (ha : Inst.Feas relaxed x a) :
    (∀ j, 0 ≤ a.semiReduce.XE j ∧ 0 ≤ a.semiReduce.XR j ∧ 0 ≤ a.semiReduce.X j) ∧
    (∀ j, a.semiReduce.XE j = 0 ∨ a.semiReduce.XR j = 0) ∧
    (∀ j, a.semiReduce.XE j ≤ a.XE j ∧ a.semiReduce.XR j ≤ a.XR j) ∧
    Inst.Feas relaxed x a.semiReduce ∧
    (∀ d, Inst.next x a.semiReduce d = Inst.next x a d) ∧
    M.instObj t G ω x a.semiReduce ≤ M.instObj t G ω x a ∧
    ((∃ j, 0 < a.XE j ∧ 0 < a.XR j ∧ 0 < M.cE j) →
      M.instObj t G ω x a.semiReduce < M.instObj t G ω x a) := by sorry

end ReverseLogisticsNEBS
