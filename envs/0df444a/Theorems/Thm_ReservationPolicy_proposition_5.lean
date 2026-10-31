-- Prove2me | Theorems.Thm_ReservationPolicy_proposition_5
-- name    : ReservationPolicy.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:27:11.602736+00:00
-- url     : https://prove2.me/theorems/2c5ec7b9-a8f2-4953-ae95-20fcec520baf
-- title:
--   Proposition 5 — welfare rises up to $s^*$ and falls after it (corrected: $z'$)
-- statement:
--   Let the parameters satisfy the standing assumptions, and let $s^*$ be the positive part of (56). Then $s^*$ is a feasible transfer, $s^*<1$, and $s^*>0$ if and only if $z>z'$, where
--   $$
--   z'=\frac{32k^2+\phi^2-8k(1-\alpha+\alpha\phi^2)}{3(32k^2+\phi^2)-16k(1+\phi^2)}.
--   $$
--   Overall welfare at equilibrium
--   1. strictly increases in the feasible transfer $s$ for $s\le s^*$;
--   2. strictly decreases in the feasible transfer $s$ for $s\ge s^*$.
--
--   So welfare has an inverted-U shape in the transfer.
--
--   Differences from the source:
--   - correction: effort e ∈ [0,1], with k > 1/4 said to keep it feasible (p.8) → effort e ≥ 0, no upper bound; reason: k = 1/3, ϕ = 1/2, α = 1/25, z = 1/5 meets every assumption and gives e*ₓ = 1740/1589 > 1, so the cap would make the closed forms false
--   - correction: d ∈ (0,1), said to be equivalent to 4kα(1−ϕ²)/((8k−1)(4k−ϕ²)) < z < 1/2 (p.9) → the z-interval alone, with no bound on d (Params.Valid); reason: the two are not equivalent: k = 1, ϕ = 1/2, α = 1/2, z = 7/100 is in the interval with d* = 3427/3300 > 1; the interval is what the proof of Proposition 1 uses (p.35) and contains the region d* ∈ (0,1)
--   - reading: each student maximizes a payoff written with the linear probability (4), the model keeping probabilities between 0 and 1 (p.9) → the true probability is used, and a best response ranges over the efforts e ≥ 0 at which it lies in (0,1), which is where (4) holds; equilibrium probabilities lie in (0,1); reason: these equilibria are exactly the paper's first-order solutions; against all e ≥ 0 they can fail to be best responses (k = 1, ϕ = 1/2, α = 1/2, z = 7/100: effort 0 pays 0 to type y, the interior effort pays −8029/2722500)
--   - correction: z′ with denominator 3(32k²+ϕ²) + 16(1+ϕ²) (57) → denominator 3(32k²+ϕ²) − 16k(1+ϕ²); reason: at k = 1, ϕ = 1/2, α = 3/10, z = 3/10 the printed z′ = 0.2231… < z, yet the maximizer is 0; solving μ₁ = 0 gives the corrected denominator
--   - correction: μ₂ with first term 16k(16k² − 3k − 5kα) + α → first term 16k(16k² − 3k − 5kα + α); reason: a misplaced bracket; see eq_56
--   - generalization: s* > 0 if z > z′ → s* > 0 if and only if z > z′; reason: p.41 adds "Otherwise, s* = 0"
--   - encoding: s* is (56), with s* = 0 when z ≤ z′ → s* := max 0 (56); reason: the two cases of p.41 in one formula
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), Proposition 5, p.23, with pp.40–41

import Mathlib
import Definitions.Def_ReservationPolicy_Params_Valid
import Definitions.Def_ReservationPolicy_IsInvestCandidate
import Definitions.Def_ReservationPolicy_IsPolicyEq
import Definitions.Def_ReservationPolicy_Feasible
import Definitions.Def_ReservationPolicy_welfare
import Definitions.Def_ReservationPolicy_Params_sStar
import Definitions.Def_ReservationPolicy_Params_zPrime

namespace ReservationPolicy

/-- **Proposition 5.** With `s*` the positive part of (56): `s*` is feasible and below `1`, it is
positive exactly when `z > z'`, and overall welfare strictly rises in `s` up to `s*` and strictly falls
after it. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), Proposition 5, p.23 (PDF 23), with pp.40–41,
`μ₂` and `z'` corrected. -/
theorem proposition_5 (P : Params) (hP : P.Valid) (b : Benchmark) (hb : IsInvestCandidate P b) :
    Feasible P b P.sStar ∧ P.sStar < 1 ∧ (0 < P.sStar ↔ P.zPrime < P.z) ∧
    (∀ (s₁ s₂ : ℝ) (o₁ o₂ : PolicyOutcome), Feasible P b s₁ → Feasible P b s₂ →
      IsPolicyEq P b s₁ o₁ → IsPolicyEq P b s₂ o₂ → s₁ < s₂ → s₂ ≤ P.sStar →
        welfare P o₁ < welfare P o₂) ∧
    (∀ (s₁ s₂ : ℝ) (o₁ o₂ : PolicyOutcome), Feasible P b s₁ → Feasible P b s₂ →
      IsPolicyEq P b s₁ o₁ → IsPolicyEq P b s₂ o₂ → P.sStar ≤ s₁ → s₁ < s₂ →
        welfare P o₂ < welfare P o₁) := by sorry

end ReservationPolicy
