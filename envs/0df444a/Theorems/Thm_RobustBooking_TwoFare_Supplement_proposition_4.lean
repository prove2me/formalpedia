-- Prove2me | Theorems.Thm_RobustBooking_TwoFare_Supplement_proposition_4
-- name    : RobustBooking.TwoFare.Supplement.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:45:24.118167+00:00
-- url     : https://prove2.me/theorems/206e8c19-e30b-4325-a477-7f2664a487c2
-- title:
--   Proposition 4 — discrete two-fare: some randomized policy has competitive ratio b(r), and none has more
-- statement:
--   Consider the discrete two-fare booking problem: integer capacity $n\ge1$, fares $f_1>f_2>0$ with $r=f_2/f_1$, unit orders accepted whole or rejected, and $b(r)=1/(2-r)$. A randomized policy is a random choice $A(\omega)$ of a deterministic discrete policy, $\omega$ drawn from a probability measure $\mu$, and its competitive ratio is
--   $$\inf_{I:\,R^*(I)>0}\frac{\mathbb E_\mu[R(A(\omega),I)]}{R^*(I)}.$$
--
--   Then:
--   1. there exists a randomized discrete policy with competitive ratio exactly $b(r)$;
--   2. every randomized discrete policy has competitive ratio at most $b(r)$.
--
--   In contrast with Theorem 2, randomization recovers the continuous ratio $b(r)$ of Theorem 1 even when $(1-b(r))n$ is fractional.
--
--   **Formalization Note** A randomized policy is a probability space $(\Omega,\mu)$ with a map $A$ into deterministic discrete policies such that, for every instance, the revenue is a measurable function of $\omega$ (it is then bounded, so the expectation is a Bochner integral of an integrable function). The existential ranges over probability spaces with $\Omega$ in `Type`; the upper bound ranges over probability spaces in any universe.
--
--   Differences from the source:
--   - encoding: "randomized booking policy" → a probability measure μ on a measurable space Ω and A : Ω → DDetPolicy with measurable revenue on every instance; reason: the paper's random choice A(P) among deterministic algorithms (p. 954); measurability makes the expectation defined.
--   - encoding: "the discrete two-fare problem" → n a natural number with 0 < n, r = f₂/f₁ with 0 < f₂ < f₁; reason: the paper's standing assumptions (pp. 952–953).
--   - reading: "the demands are integer and each order must be entirely accepted or rejected" → an instance is a finite sequence of unit orders (integer demand = number of unit orders of a fare), each accepted whole or rejected; reason: p. 956 makes each order one unit with x_i ∈ {0,1} and §1 counts requests as units; with indivisible multi-unit orders Theorem 2 would fail (n = 3, r = 1/2: one low order of 3 units exceeds the booking limit 2, giving ratio 0 instead of 2/3).
--   - encoding: "competitive ratio = inf over all input sequences of v′(I)/v*(I)" → the infimum is over instances with v*(I) > 0; reason: the quotient is undefined when v*(I) = 0, which for n ≥ 1 and positive fares happens only on the empty instance.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 954, Proposition 4

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_Supplement_DiscreteTwoFare

open MeasureTheory

namespace RobustBooking.TwoFare.Supplement

/-- Proposition 4 (Ball–Queyranne 2009, p. 954). In the discrete two-fare problem with fares
`f₁ > f₂ > 0`, `r = f₂ / f₁` and integer capacity `n ≥ 1`, some randomized discrete policy (a random
choice of a deterministic discrete policy) has competitive ratio exactly `b(r)`, and every
randomized discrete policy has competitive ratio at most `b(r)`. -/
theorem proposition_4 (f₁ f₂ : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (n : ℕ) (hn : 0 < n) :
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
      ∃ A : Ω → DDetPolicy, (∀ I : List FareClass, Measurable fun ω => revenue f₁ f₂ n (A ω) I) ∧
        randCompetitiveRatio f₁ f₂ n μ A = b (f₂ / f₁)) ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (A : Ω → DDetPolicy), (∀ I : List FareClass, Measurable fun ω => revenue f₁ f₂ n (A ω) I) →
        randCompetitiveRatio f₁ f₂ n μ A ≤ b (f₂ / f₁) := by sorry

end RobustBooking.TwoFare.Supplement
