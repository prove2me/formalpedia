-- Prove2me | Theorems.Thm_TwoSidedMatching_Guarantee_theorem_2
-- name    : TwoSidedMatching.Guarantee.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:28.082068+00:00
-- url     : https://prove2.me/theorems/8f6b3f98-53a9-497d-a174-456d335e291e
-- title:
--   Theorem 2 — waiting-adjusted fixed prices approach fluid profit
-- statement:
--   Let J be the expected profit from waiting-adjusted fixed prices with greedy matching and myopic requests, J̄* the optimum of (D), and E[J̄(Hᵀ)] the expected clairvoyant matching value. For regular continuous distributions, positive rates and horizon, nonnegative waiting costs, and c̲ < v̄, the relevant expectations and denominators are finite and positive, and
--
--   $$\frac{J}{\bar J^*}\ge1-\left(1+\frac{2(b+h)T}{3(p^*-w^*)}\right)\frac1{\sqrt{\mu^*}}.$$
--
--   When J ≥ 0, the clairvoyant benchmark also gives J/E[J̄(Hᵀ)] ≥ J/J̄*. If rates scale as λᵈ⁽ⁿ⁾ = n^αᵈ λᵈ and λˢ⁽ⁿ⁾ = n^αˢ λˢ, with αᵈ, αˢ > 0 and n ≥ 1, a constant C depending on the base system but not n gives
--
--   $$\frac{J^{(n)}}{\bar J^{*,(n)}}\ge1-\frac C{\sqrt{n^{\min(\alpha_d,\alpha_s)}}},$$
--
--   and the same conditional clairvoyant comparison holds at each scale. This is the finite-market and asymptotic profit guarantee.
--
--   **Formalization Note** Strict c̲ < v̄ makes μ* and p*−w* positive. The printed first comparison requires J ≥ 0: its algebra fails with a negative numerator. Density continuity and nonnegative support endpoints ensure well-defined inverse prices and fluid admissibility. Myopic behavior is the equilibrium of Theorem 1, built into this model rather than re-proved.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), main text p. 22, Theorem 2 (PDF p. 23); Supplemental Note pp. 12–15 (PDF pp. 52–55)

import Mathlib
import Definitions.Def_TwoSidedMatching_Guarantee_Market

open MeasureTheory

namespace TwoSidedMatching.Guarantee

/-- Main text Theorem 2. The upper-benchmark ratio comparison is conditional
on nonnegative profit, as required by the printed chain's algebra. -/
theorem theorem_2 (E : Environment) (lamD lamS T b h : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hloB : 0 ≤ E.loB) (hloS : 0 ≤ E.loS)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h) :
    let J := policyProfit E lamD lamS T b h
    let EJ := ∫ ω, Jbar E b h ω ∂P E lamD lamS T
    let Js := fluidValue E lamD lamS T
    Integrable (profit E lamD lamS T b h) (P E lamD lamS T) ∧
    Integrable (Jbar E b h) (P E lamD lamS T) ∧
    0 < muStar E lamD lamS T ∧
    wStar E lamD lamS T < pStar E lamD lamS T ∧
    0 < EJ ∧ 0 < Js ∧
    1 - (1 + (2 / 3 : ℝ) * ((b + h) * T) /
      (pStar E lamD lamS T - wStar E lamD lamS T)) /
      Real.sqrt (muStar E lamD lamS T) ≤ J / Js ∧
    (0 ≤ J → J / Js ≤ J / EJ) ∧
    (∀ αd αs : ℝ, 0 < αd → 0 < αs →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
        let ld := (n : ℝ) ^ αd * lamD
        let ls := (n : ℝ) ^ αs * lamS
        let Jn := policyProfit E ld ls T b h
        let EJn := ∫ ω, Jbar E b h ω ∂P E ld ls T
        let Jsn := fluidValue E ld ls T
        Integrable (profit E ld ls T b h) (P E ld ls T) ∧
        Integrable (Jbar E b h) (P E ld ls T) ∧
        0 < EJn ∧ 0 < Jsn ∧
        1 - C / Real.sqrt ((n : ℝ) ^ min αd αs) ≤ Jn / Jsn ∧
        (0 ≤ Jn → Jn / Jsn ≤ Jn / EJn)) := by sorry

end TwoSidedMatching.Guarantee
