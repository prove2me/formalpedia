-- Prove2me | Theorems.Thm_TimeScaleAvg_eq_53
-- name    : TimeScaleAvg.eq_53
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:28.023655+00:00
-- url     : https://prove2.me/theorems/79c3f914-dd59-499f-8a15-5c80c537872c
-- title:
--   Eq. (53) — Jensen's inequality for $\mu_s$
-- statement:
--   Let $f$ satisfy $(\mathcal A)$, let $\alpha>1$ and $0<s_0\le s$, and let $y$ be continuous on $[s_0,s]$. Then
--
--   $$
--   f\Bigl(\int_{s_0}^{s}y(u)\,d\mu_s(u)\Bigr)-\inf_{\mathcal H}f\le\int_{s_0}^{s}\bigl(f(y(u))-\inf_{\mathcal H}f\bigr)\,d\mu_s(u).
--   $$
--
--   This is where the averaging interpretation produces the value rate of Theorem 2.
--
--   Differences from the source:
--   - generalization: y the solution of (32) → y any map continuous on [s₀,s]; reason: the solution of (32) is continuous, so the source inequality is the special case
--   - generalization: (53), inside the proof of clause (v), under "If α > 3" → (53), for every α > 1; reason: the statement with 1 < α contains the case 3 < α used by the source, and the argument never uses 3 < α
--   - reading: the time origin t₀ > 0 fixed on p.2, with s₀ given by t₀ = τ(s₀); the statement does not repeat it → hypothesis 0 < s₀; reason: a standing assumption of the paper, not repeated in the statement
--   - encoding: inf_H f → the real infimum ⨅ y, f y; reason: S ≠ ∅ makes f bounded below, so the real infimum is the true one
-- source:
--   Attouch, Boţ & Nguyen, Fast Convex Optimization via Time Scale and Averaging of the Steepest Descent, arXiv:2208.08260v3, Eq. (53), p.9

import Mathlib
import Definitions.Def_TimeScaleAvg_AssumptionA
import Definitions.Def_TimeScaleAvg_muS

open Filter Topology MeasureTheory

namespace TimeScaleAvg

/-- Eq. (53), Jensen's inequality for `μ_s` (Attouch, Boţ & Nguyen, arXiv:2208.08260v3, p.9). For
`y` continuous on `[s₀, s]`,
`f(∫_{s₀}^{s} y(u) dμ_s(u)) - inf_H f ≤ ∫_{s₀}^{s} (f(y(u)) - inf_H f) dμ_s(u)`.

**Formalization Note.** The page has the solution `y` of (32), inside the proof of clause (v) under
`α > 3`. The inequality is stated here for every `y` continuous on `[s₀, s]` and every `α > 1`.
Continuity makes both integrals integrals of integrable functions, since `μ_s` is a finite measure
carried by `[s₀, s]`. -/
theorem eq_53 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : H → ℝ} (hf : AssumptionA f) {α s₀ s : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α) (hs : s₀ ≤ s)
    {y : ℝ → H} (hy : ContinuousOn y (Set.Icc s₀ s)) :
    f (∫ u, y u ∂(muS α s₀ s)) - (⨅ z, f z) ≤ ∫ u, (f (y u) - ⨅ z, f z) ∂(muS α s₀ s) := by sorry

end TimeScaleAvg
