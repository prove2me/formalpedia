-- Prove2me | Theorems.Thm_TightQLearning_eq_68_70
-- name    : TightQLearning.eq_68_70
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:31:18.78457+00:00
-- url     : https://prove2.me/theorems/baa0373e-34f7-4534-b663-62dd1784202e
-- title:
--   (68a), (68b), (69), (70) — size and sum of the weights $\eta_i^{(t)}$ (corrected: $\tau\ge1$ in (70))
-- statement:
--   Let $\eta_i^{(t)}$ be the weights of (36). For $t\ge1$,
--   $$\sum_{i=0}^t\eta_i^{(t)}=1,$$
--   and for $1\le\tau\le t$,
--   $$\sum_{i=\tau}^t\eta_i^{(t)}=1-\prod_{j=\tau}^t(1-\eta_j).$$
--   Now let $T\ge2$, $\gamma\in(0,1)$, $c_1\ge c_2>0$, $c_4>0$, let the rates obey (16a), let $\beta=c_4(1-\gamma)/\log T$, and let $t\le T$ with $t\ge T/(c_2\log T)$. If $c_1c_2\le c_4/8$ and $c_1(1-\gamma)T/\log^3T\ge1$, then for every $i\le(1-\beta)t$,
--   $$\eta_i^{(t)}<\frac1{2T^2}.$$
--   If $1-\beta\ge\frac12$, then for every $i\le t$ with $i>(1-\beta)t$,
--   $$\eta_i^{(t)}\le\frac{2\log^4T}{(1-\gamma)T}.$$
--
--   The bounds split the unrolled recursion into an old part, which is negligible, and a recent part, in which no single sample carries much weight. That is what Freedman's inequality needs.
--
--   Differences from the source:
--   - correction: (70) is printed for any τ ≤ t → 1 ≤ τ ≤ t; reason: the printed claim is false at τ = 0: for t = 1 and η_0 = η_1 = 1/2 the left side is 1 and the right side is 3/4 (verified in Lean); the page uses (70) only with τ ≥ 1
--   - encoding: (36) has colliding cases at t = 0 → 1 ≤ t in (69); reason: the weights are not defined by the page at t = 0
--   - generalization: (69), (70) for rates of the band → any real sequence η; reason: both are algebraic identities
--   - generalization: (65) derived from (63) → 1 ≤ c₁(1−γ)T/log³T as the hypothesis of (68a); reason: (68a) uses (63) only through this consequence
--   - generalization: c₄ is one universal constant → any c₄ > 0 with c₁c₂ ≤ c₄/8; reason: the paper's c₄ is one such value
--   - reading: (68b) uses (1−β)t ≥ t/2 from "c₄ small" → the hypothesis 1/2 ≤ 1 − β; reason: the page states it inside the case distinction and it holds for its c₄
--   - encoding: (16a) divides by log³T, which is undefined at T = 1 → the hypothesis 2 ≤ T; reason: it excludes only T = 0 and T = 1, where the printed condition is undefined; Lean's x/0 = 0 would make the statement false there (verified)
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), (68a), (68b), (69), (70), p.21

import Mathlib
import Definitions.Def_TightQLearning_weight
import Definitions.Def_TightQLearning_RateBand

namespace TightQLearning

/-- Size and sum of the weights `η_i^{(t)}` (Li, Cai, Chen, Wei & Chi, arXiv:2102.06548v4, p.21):
(69), (70) and the bounds (68a), (68b), with `β = c₄(1−γ)/log T` (66) and
`t ≥ T/(c₂ log T)` (67).

**Formalization Note.** (70) is printed "for any τ ≤ t" and is false at `τ = 0`, so it is stated
for `1 ≤ τ ≤ t`. The comparisons `i ≤ (1−β)t` are real comparisons. The bound (68a) carries the
paper's `c₁c₂ ≤ c₄/8` and the consequence (65) of (63), `1 ≤ c₁(1−γ)T/log³T`; (68b) carries the
page's `(1−β)t ≥ t/2`, as `1/2 ≤ 1 − β`. -/
theorem eq_68_70 :
    (∀ (η : ℕ → ℝ) (t : ℕ), 1 ≤ t → ∑ i ∈ Finset.range (t + 1), weight η t i = 1) ∧
    (∀ (η : ℕ → ℝ) (t τ : ℕ), 1 ≤ τ → τ ≤ t →
      ∑ i ∈ Finset.Icc τ t, weight η t i = 1 - ∏ j ∈ Finset.Icc τ t, (1 - η j)) ∧
    (∀ (c₁ c₂ c₄ γ : ℝ) (T t i : ℕ) (η : ℕ → ℝ), 0 < c₂ → c₂ ≤ c₁ → 0 < c₄ →
      c₁ * c₂ ≤ c₄ / 8 → 0 < γ → γ < 1 → 2 ≤ T → RateBand c₁ c₂ γ T η →
      1 ≤ c₁ * (1 - γ) * (T : ℝ) / Real.log T ^ 3 →
      (T : ℝ) / (c₂ * Real.log T) ≤ t → t ≤ T → i ≤ t →
      (i : ℝ) ≤ (1 - c₄ * (1 - γ) / Real.log T) * t →
      weight η t i < 1 / (2 * (T : ℝ) ^ 2)) ∧
    (∀ (c₁ c₂ c₄ γ : ℝ) (T t i : ℕ) (η : ℕ → ℝ), 0 < c₂ → c₂ ≤ c₁ → 0 < c₄ →
      0 < γ → γ < 1 → 2 ≤ T → RateBand c₁ c₂ γ T η →
      (T : ℝ) / (c₂ * Real.log T) ≤ t → t ≤ T → i ≤ t →
      (1 - c₄ * (1 - γ) / Real.log T) * t < (i : ℝ) →
      1 / 2 ≤ 1 - c₄ * (1 - γ) / Real.log T →
      weight η t i ≤ 2 * Real.log T ^ 4 / ((1 - γ) * (T : ℝ))) := by sorry

end TightQLearning
