-- Prove2me | Theorems.Thm_PolyVoting_total_tendsto_atTop
-- name    : PolyVoting.total_tendsto_atTop
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:03.901206+00:00
-- url     : https://prove2.me/theorems/f155c844-665d-4a5b-8249-b6922a0a9afe
-- title:
--   p.6 (proof of Proposition 2 (ii)) — $N_t\to\infty$ almost surely
-- statement:
--   For every $\alpha\ge0$, with probability one the volume diverges:
--   $$N_t\to\infty\quad\text{as }t\to\infty.$$
--
--   This drives the decay of the voting power and the embedding of the Pólya urn: infinitely many stakes are eventually awarded, even when $\sum_t(N+t)^{-\alpha}<\infty$.
--
--   Differences from the source:
--   - encoding: the Poly(α) rule described by (2.3)–(2.6), K ∈ ℕ₊ bidders, stakes n_{k,t} → `Model μ K α n₀`: the joint conditional one-step law, stakes in Fin K → ℕ, real α ≥ 0 with Real.rpow, and 1 ≤ N; reason: the conditional one-step law and n₀ determine the law of the chain; 1 ≤ N only keeps N_t^{−α} defined
-- source:
--   Tang & Yao, Polynomial Voting Rules, arXiv:2206.10105v5, p.6, proof of Proposition 2 (ii), "It is clear that with probability one Nt → ∞ as t → ∞"

import Mathlib
import Definitions.Def_PolyVoting_Model

open MeasureTheory Filter

namespace PolyVoting

/-- **The volume diverges** (Tang & Yao, *Polynomial Voting Rules*, arXiv:2206.10105v5, p.6, proof of
Proposition 2 (ii)): with probability one `N_t → ∞` as `t → ∞`, for every `α ≥ 0`. -/
theorem total_tendsto_atTop {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : ℕ} {α : ℝ} {n₀ : Fin K → ℕ} (M : Model μ K α n₀) :
    ∀ᵐ ω ∂μ, Tendsto (fun t => M.total t ω) atTop atTop := by sorry

end PolyVoting
