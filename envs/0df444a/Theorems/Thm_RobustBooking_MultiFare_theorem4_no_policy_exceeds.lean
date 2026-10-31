-- Prove2me | Theorems.Thm_RobustBooking_MultiFare_theorem4_no_policy_exceeds
-- name    : RobustBooking.MultiFare.theorem4_no_policy_exceeds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T23:43:54.768463+00:00
-- url     : https://prove2.me/theorems/63ac0b0a-6fc3-4bdd-a27c-14705beb834a
-- title:
--   Theorem 4 — no booking policy, deterministic or randomized, has competitive ratio larger than 1/Δ
-- statement:
--   Consider the continuous $m$-fare booking problem with $m \ge 2$, fares $f_1 > f_2 > \dots > f_m > 0$ and capacity $n > 0$, and let $\Delta = m - \sum_{i=2}^m f_i/f_{i-1}$ (Eq. (6)). Then every deterministic online policy $B$ satisfies
--   $$c(B) \le \frac{1}{\Delta},$$
--   and every randomized policy — a random choice $A(\omega)$ of a deterministic policy, $\omega \sim \mu$ for a probability measure $\mu$ on any measurable space $\Omega$, such that for each instance the revenue $\omega \mapsto R(A(\omega), I)$ is measurable — satisfies
--   $$c(\mu, A) = \inf_{I:\, v^*(I) > 0} \frac{\mathbb{E}_\mu[R(A(\omega), I)]}{v^*(I)} \le \frac{1}{\Delta}.$$
--   This is the negative half of the paper's main multi-fare result: no online policy, even with randomization, can guarantee more than a $1/\Delta$ fraction of the offline optimum.
--
--   **Formalization Note.** Competitive ratios are those of the booking model (infimum over instances with positive offline optimum). The paper's §2.1 assumes $m \ge 3$; the statement is made for $m \ge 2$. Measurability of the revenue in $\omega$ is the standing requirement for the expectation to be defined; the revenue is bounded for each instance, so it is then integrable.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 957, Theorem 4

import Mathlib
import Definitions.Def_RobustBooking_MultiFare_BookingModel
import Definitions.Def_RobustBooking_MultiFare_ProtectionLevels

open MeasureTheory

namespace RobustBooking.MultiFare

/-- Theorem 4 (p. 957): for the continuous `m`-fare problem (fares `f 1 > ⋯ > f m > 0`,
`m ≥ 2`, capacity `n > 0`), no booking policy, deterministic or randomized, has a
competitive ratio larger than `1/Δ`. A randomized policy is a random choice `A ω` of a
deterministic policy, `ω ∼ μ` on an arbitrary probability space, with the revenue on
each instance measurable in `ω`. -/
theorem theorem4_no_policy_exceeds (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → DetPolicy) (hA : ∀ I : List Request, IsInstance m I →
      Measurable fun ω => revenue f n (A ω) I) :
    (∀ B : DetPolicy, competitiveRatio m f n B ≤ 1 / Delta m f) ∧
    randCompetitiveRatio m f n μ A ≤ 1 / Delta m f := by sorry

end RobustBooking.MultiFare
