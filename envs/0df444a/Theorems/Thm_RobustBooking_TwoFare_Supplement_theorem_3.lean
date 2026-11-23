-- Prove2me | Theorems.Thm_RobustBooking_TwoFare_Supplement_theorem_3
-- name    : RobustBooking.TwoFare.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:46:55.056368+00:00
-- url     : https://prove2.me/theorems/a436d0c6-d99d-4212-932d-6bfecf1d2c2d
-- title:
--   Theorem 3 — discrete two-fare: a random protection level gives ratio b(r) iff its expectation is (1 − b(r))n
-- statement:
--   Consider the discrete two-fare booking problem: integer capacity $n\ge1$, fares $f_1>f_2>0$ with $r=f_2/f_1$, unit orders accepted whole or rejected, and $b(r)=1/(2-r)$. A **randomized protection-level policy** draws an integer protection level $\theta\in\{0,1,\dots,n\}$ from a probability law $\mu$ before the first order and then runs the discrete nested policy with protection level $\theta$ (booking limit $n-\theta$ for low-fare orders).
--
--   For every probability law $\mu$ on $\{0,\dots,n\}$, this randomized policy has competitive ratio $b(r)$ if and only if
--   $$\mathbb E_\mu[\theta]=(1-b(r))\,n.$$
--
--   By Proposition 4, $b(r)$ is the largest competitive ratio of any randomized discrete policy, so the theorem characterizes the optimal randomized protection-level policies, among them the two-point policy of the proof of Proposition 4 ($\theta=0$ with probability $b(r)$, $\theta=n$ with probability $1-b(r)$).
--
--   **Formalization Note** The law $\mu$ is an arbitrary probability measure on `Fin (n + 1)`, and the competitive ratio is the randomized ratio of the discrete model applied to the random policy $\theta\mapsto$ `nestedD n θ`. Protection levels are integers, as the paper fixes for the discrete problem (p. 952).
--
--   Differences from the source:
--   - reading: "a randomized booking policy … its protection level" → a random integer protection level θ with an arbitrary law μ on {0, …, n}, followed by the discrete nested policy at θ; reason: only a policy that is a random protection level has "its protection level"; this is the class of the proof of Proposition 4 (p. 954), and p. 952 makes discrete protection levels integers; the preceding sentence of p. 955 speaks of "all optimal randomized booking policies", but the condition has no meaning for a policy without a protection level, and integrality is needed (n = 2, r = 1/2, θ = 2/3 surely has the stated mean and ratio 1/2 < b(r) = 2/3).
--   - reading: "has optimal competitive ratio b(r)" → its competitive ratio equals b(r); reason: that b(r) is the optimal value is Proposition 4.
--   - encoding: "the discrete two-fare booking problem" → n a natural number with 0 < n, r = f₂/f₁ with 0 < f₂ < f₁; reason: the paper's standing assumptions (pp. 952–953).
--   - reading: "the demands are integer and each order must be entirely accepted or rejected" → an instance is a finite sequence of unit orders (integer demand = number of unit orders of a fare), each accepted whole or rejected; reason: p. 956 makes each order one unit with x_i ∈ {0,1} and §1 counts requests as units; with indivisible multi-unit orders Theorem 2 would fail (n = 3, r = 1/2: one low order of 3 units exceeds the booking limit 2, giving ratio 0 instead of 2/3).
--   - encoding: "competitive ratio = inf over all input sequences of v′(I)/v*(I)" → the infimum is over instances with v*(I) > 0; reason: the quotient is undefined when v*(I) = 0, which for n ≥ 1 and positive fares happens only on the empty instance.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 955, Theorem 3 (randomized protection levels as in the proof of Proposition 4, p. 954)

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_Supplement_DiscreteTwoFare

open MeasureTheory

namespace RobustBooking.TwoFare.Supplement

/-- Theorem 3 (Ball–Queyranne 2009, p. 955). In the discrete two-fare problem with fares
`f₁ > f₂ > 0`, `r = f₂ / f₁` and integer capacity `n ≥ 1`, let the protection level `θ` be drawn from
an arbitrary probability law `μ` on `{0, 1, …, n}` before the first order, and then the discrete
nested policy with protection level `θ` be run. This randomized policy has competitive ratio
`b(r)` if and only if `E[θ] = (1 - b(r)) n`. -/
theorem theorem_3 (f₁ f₂ : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (n : ℕ) (hn : 0 < n)
    (μ : Measure (Fin (n + 1))) [IsProbabilityMeasure μ] :
    randCompetitiveRatio f₁ f₂ n μ (fun θ => nestedD n θ.val) = b (f₂ / f₁) ↔
      ∫ θ, (θ.val : ℝ) ∂μ = (1 - b (f₂ / f₁)) * n := by sorry

end RobustBooking.TwoFare.Supplement
