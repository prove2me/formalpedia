-- Prove2me | Theorems.Thm_TightQLearning_eq_90_94
-- name    : TightQLearning.eq_90_94
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:32:11.159538+00:00
-- url     : https://prove2.me/theorems/5ca55586-b356-4f40-83f2-b4e840fb50d3
-- title:
--   (90)–(94) — solving the recursion: $\|\Delta_T\|_\infty\le c_8(\sqrt x+x)$
-- statement:
--   For every $c_2>0$ there are constants $c_8,c_9>0$ with the following property. Let $\gamma\in(0,1)$, $x\ge0$, $T\ge2$ with $T\ge c_9/(1-\gamma)^3$, and let $(a_t)$ be a real sequence with $0\le a_t\le\frac1{1-\gamma}$ for $t\le T$ and
--   $$a_t\le30\sqrt{x\Big(1+\max_{t/2\le i<t}a_i\Big)}\qquad\text{for }2\le t\le T,\ t\ge\frac T{c_2\log T}.$$
--   Then
--   $$a_T\le c_8\big(\sqrt x+x\big).$$
--
--   Applied with $a_t=\|\Delta_t\|_\infty$ and $x=\frac{(\log^4T)(\log\frac{|\mathcal S||\mathcal A|T}\delta)}{\gamma^2(1-\gamma)^4T}$, this is the passage from the recursion (90) to the final bound (94). It is the purely deterministic part of the proof, carried out on dyadic windows.
--
--   Differences from the source:
--   - encoding: (16a) divides by log³T, which is undefined at T = 1 → the hypothesis 2 ≤ T; reason: it excludes only T = 0 and T = 1, where the printed condition is undefined; Lean's x/0 = 0 would make the statement false there (verified)
--   - encoding: max over t/2 ≤ i < t, which is undefined for t = 1 → the hypothesis 2 ≤ t, and windowMax over a nonempty window; reason: it excludes only the case where the printed maximum is undefined
--   - generalization: a_t = ‖Δ_t‖_∞ on the event (90), x the printed ratio → any real sequence a_t and any x ≥ 0; reason: B.4 is deterministic given (90) and (92); the printed case is a special case
--   - reading: B.4 has no numbered statement; c₈ is "some constant", k = c₇ log log(1/(1−γ)) and 2^k T/(c₂ log T) < T → ∀ c₂ > 0, ∃ c₈, c₉ > 0, under T ≥ c₉/(1−γ)³; reason: c₈ depends on c₂ because 2^k must stay below c₂ log T; T ≥ c₉/(1−γ)³ is what that k needs, and (63) implies it
--   - reading: "for all t ≥ T/(c₂ log T)" → T/(c₂ log T) ≤ t ≤ T; reason: (91) works in this range
-- source:
--   Li, Cai, Chen, Wei & Chi, Is Q-Learning Minimax Optimal? A Tight Sample Complexity Analysis, arXiv:2102.06548v4 (https://arxiv.org/abs/2102.06548v4), (90)–(94), Appendix B.4, pp.26–28

import Mathlib
import Definitions.Def_TightQLearning_windowMax

namespace TightQLearning

/-- Solving the recursion (90)–(94) (Li, Cai, Chen, Wei & Chi, arXiv:2102.06548v4, Appendix B.4,
pp.26–28), as a deterministic statement on a real sequence `a_t` (the page's `‖Δ_t‖_∞`) with `x`
in place of `(log⁴T)(log(|S||A|T/δ))/(γ²(1−γ)⁴T)`: if `0 ≤ a_t ≤ 1/(1−γ)` (92) and
`a_t ≤ 30 √(x (1 + max_{t/2≤i<t} a_i))` for `t ≥ T/(c₂ log T)` (90), then
`a_T ≤ c₈(√x + x)` (94).

**Formalization Note.** B.4 has no numbered statement. `c₈` depends only on `c₂`, as on the page,
where `2^k` must stay below `c₂ log T`. `T ≥ c₉/(1−γ)³` is what the page's choice
`k = c₇ log log(1/(1−γ))` needs, and it follows from (63). -/
theorem eq_90_94 :
    ∀ c₂ : ℝ, 0 < c₂ → ∃ c₈ : ℝ, 0 < c₈ ∧ ∃ c₉ : ℝ, 0 < c₉ ∧
      ∀ (γ x : ℝ) (T : ℕ) (a : ℕ → ℝ), 0 < γ → γ < 1 → 0 ≤ x → 2 ≤ T →
        (T : ℝ) ≥ c₉ / (1 - γ) ^ 3 →
        (∀ t, t ≤ T → 0 ≤ a t ∧ a t ≤ 1 / (1 - γ)) →
        (∀ (t : ℕ) (ht : 2 ≤ t), (T : ℝ) / (c₂ * Real.log T) ≤ t → t ≤ T →
          a t ≤ 30 * Real.sqrt (x * (1 + windowMax t ht a))) →
        a T ≤ c₈ * (Real.sqrt x + x) := by sorry

end TightQLearning
