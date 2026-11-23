-- Prove2me | Theorems.Thm_RobustBooking_TwoFare_Supplement_theorem_2
-- name    : RobustBooking.TwoFare.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:44:42.102803+00:00
-- url     : https://prove2.me/theorems/4c9428f8-b0ec-452f-96cd-eb1f3408a566
-- title:
--   Theorem 2 — discrete two-fare: the nested policy at θ_D(r, n) has competitive ratio c(n − θ_D(r, n)), best among deterministic policies
-- statement:
--   Consider the discrete two-fare booking problem: integer capacity $n\ge1$, fares $f_1>f_2>0$ with $r=f_2/f_1$, and instances that are finite sequences of unit high- and low-fare orders, each accepted whole or rejected. Let $c(x)=\min\{(n-(1-r)x)/n,\;x/n\}$ (Eq. (3)) and let $\theta_D(r,n)$ be the optimum rounding of Eq. (4).
--
--   Then the nested policy with protection level $\theta_1=\theta_D(r,n)$ (booking limit $n-\theta_D(r,n)$ for low-fare orders) has competitive ratio exactly
--   $$c\big(n-\theta_D(r,n)\big),$$
--   and every deterministic online policy for the discrete problem has competitive ratio at most $c(n-\theta_D(r,n))$.
--
--   This is the discrete counterpart of Theorem 1: when $(1-b(r))n$ is fractional the best deterministic ratio is the value of $c$ at the better of the two integer roundings of $b(r)n$, which is at most $b(r)$.
--
--   **Formalization Note** The ratio is the `sInf` over discrete instances with positive offline optimum. The "best possible" clause ranges over all deterministic all-or-none policies, not over randomized ones and not only over protection-level policies.
--
--   Differences from the source:
--   - encoding: "the discrete two-fare booking problem" → capacity a natural number n with 0 < n, and r = f₂/f₁ with 0 < f₂ < f₁; reason: the paper's standing assumptions (pp. 952–953); n = 0 has no instance with positive optimum, so the ratio is undefined there.
--   - reading: "the demands are integer and each order must be entirely accepted or rejected" → an instance is a finite sequence of unit orders (integer demand = number of unit orders of a fare), each accepted whole or rejected; reason: p. 956 makes each order one unit with x_i ∈ {0,1} and §1 counts requests as units; with indivisible multi-unit orders Theorem 2 would fail (n = 3, r = 1/2: one low order of 3 units exceeds the booking limit 2, giving ratio 0 instead of 2/3).
--   - encoding: "competitive ratio = inf over all input sequences of v′(I)/v*(I)" → the infimum is over instances with v*(I) > 0; reason: the quotient is undefined when v*(I) = 0, which for n ≥ 1 and positive fares happens only on the empty instance.
--   - encoding: "all deterministic online booking policies" → every function from the history (earlier classes and decisions) and the current class to accept/reject, with acceptance switched off once n orders are accepted; reason: such functions, run under the capacity constraint, are exactly the feasible nonanticipative all-or-none policies.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 954, Theorem 2, with Eqs. (3)–(4)

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_Supplement_DiscreteTwoFare

namespace RobustBooking.TwoFare.Supplement

/-- Theorem 2 (Ball–Queyranne 2009, p. 954). In the discrete two-fare problem with fares
`f₁ > f₂ > 0`, `r = f₂ / f₁` and integer capacity `n ≥ 1`, the nested policy with protection level
`θ_D(r, n)` has competitive ratio exactly `c(n - θ_D(r, n))`, and no deterministic discrete policy
has a larger competitive ratio. -/
theorem theorem_2 (f₁ f₂ : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (n : ℕ) (hn : 0 < n) :
    competitiveRatio f₁ f₂ n (nestedD n (thetaD (f₂ / f₁) n)) =
        cfun (f₂ / f₁) n ((n : ℝ) - (thetaD (f₂ / f₁) n : ℝ)) ∧
    ∀ A : DDetPolicy,
      competitiveRatio f₁ f₂ n A ≤ cfun (f₂ / f₁) n ((n : ℝ) - (thetaD (f₂ / f₁) n : ℝ)) := by sorry

end RobustBooking.TwoFare.Supplement
