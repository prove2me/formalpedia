-- Prove2me | Theorems.Thm_RevShareCoord_Wholesale_efficiency_formula_monotone
-- name    : RevShareCoord.Wholesale.efficiency_formula_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:07:05.567081+00:00
-- url     : https://prove2.me/theorems/6301a88f-4b7c-4346-b7d5-86874b4b5957
-- title:
--   Sec. 4.1.1, p. 18 — (2+α)/(1+α)^((1+α)/α) increases in α, from 2/e at 0⁺ to 1 at ∞
-- statement:
--   Let
--
--   $$
--   E(\alpha) = \frac{2+\alpha}{(1+\alpha)^{\frac{1+\alpha}{\alpha}}}, \qquad \alpha > 0 .
--   $$
--
--   Then $E$ is strictly increasing on $(0,\infty)$,
--
--   $$
--   \lim_{\alpha \to 0^+} E(\alpha) = \frac{2}{e}, \qquad \lim_{\alpha\to\infty} E(\alpha) = 1 .
--   $$
--
--   $E(\alpha)$ is the efficiency of the supplier's optimal wholesale-price contract when marginal revenue is $1 - q^\alpha$. The statement says that efficiency improves as the marginal revenue curve becomes more concave, starting from about $73.6\%$ for very convex marginal revenue and approaching full coordination only in the limit.
--
--   **Formalization Note** The page says "Efficiency is a decreasing function of $\alpha$, i.e., efficiency improves as the marginal revenue curve becomes more concave". The first half is a slip: $E(0^+) = 2/e \approx 0.7358$, $E(1) = 0.75$, $E(10) \approx 0.8583$, $E(1000) \approx 0.9941$, so $E$ increases, which is what the second half and the two limits say. The statement formalizes the corrected, increasing form. The page's numerical gloss "$2/e \approx 0.73$" is not formalized.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 18 (PDF 19), Section 4.1.1, 'Efficiency is a decreasing function of α ... the system is coordinated in the limit' (monotonicity corrected)

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

namespace RevShareCoord.Wholesale

/-- Sec. 4.1.1 (p. 18), corrected: the function `E(α) = (2+α)/(1+α)^{(1+α)/α}` is strictly
increasing on `(0, ∞)` (the printed "decreasing" is a slip), tends to `2/e` as `α → 0⁺`,
and tends to `1` as `α → ∞`. -/
theorem efficiency_formula_monotone :
    StrictMonoOn (fun α : ℝ => (2 + α) / (1 + α) ^ ((1 + α) / α)) (Set.Ioi 0) ∧
      Filter.Tendsto (fun α : ℝ => (2 + α) / (1 + α) ^ ((1 + α) / α))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 / Real.exp 1)) ∧
      Filter.Tendsto (fun α : ℝ => (2 + α) / (1 + α) ^ ((1 + α) / α))
        Filter.atTop (nhds 1) := by sorry

end RevShareCoord.Wholesale
