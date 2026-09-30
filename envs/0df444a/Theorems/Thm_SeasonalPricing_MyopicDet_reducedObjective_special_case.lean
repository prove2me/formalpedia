-- Prove2me | Theorems.Thm_SeasonalPricing_MyopicDet_reducedObjective_special_case
-- name    : SeasonalPricing.MyopicDet.reducedObjective_special_case
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:02:38.070272+00:00
-- url     : https://prove2.me/theorems/7efdbc4d-3b24-456a-8e05-67813277f1df
-- title:
--   Proof of Proposition 4, the special case $\rho \le e^{-2+e^{-1}}$ — the maximizer $p_1^* = e^{-1+e^{-1}}$, $p_2^* = p_1^*/e$
-- statement:
--   Let $0 < \rho \le e^{-2+e^{-1}}$ and
--
--   $$
--   G(p_1, p_2) = (p_1 - p_2)\cdot\frac{\ln p_1}{\ln\rho} + p_2\cdot\frac{\ln p_2}{\ln\rho}, \qquad \rho \le p_2 \le p_1 \le 1 .
--   $$
--
--   Write $p_1^* = e^{-1+e^{-1}}$ and $p_2^* = p_1^*/e = e^{-2+e^{-1}}$. Then:
--
--   1. the maximum of $G$ over the region $\rho \le p_2 \le p_1 \le 1$ exists and equals $-e^{-1+e^{-1}}/\ln\rho$;
--   2. $(p_1^*, p_2^*)$ lies in the region ($\rho \le p_2^*$ and $p_1^* \le 1$) and $G(p_1^*, p_2^*) = -e^{-1+e^{-1}}/\ln\rho$;
--   3. $(p_1^*, p_2^*)$ is the only maximizer in the region.
--
--   The paper states "the special case $\rho \le e^{-2+e^{-1}}$ could be easily solved analytically to yield the results stated in the proposition"; this item is that calculation. Uniqueness is stated because Proposition 4 names "the prices $p_1^*$ and $p_2^*$ that solve the problem" and gives their values.
-- source:
--   Aviv and Pazgal, Optimal Pricing of Seasonal Products in the Presence of Forward-Looking Consumers, Manufacturing & Service Operations Management 10(3), 2008, p. 351, Proposition 4 (p*₁ = e^{−1+e^{−1}}, p*₂ = p*₁/e); p. 359, Proof of Proposition 4 ("The special case …")

import Mathlib
import Definitions.Def_SeasonalPricing_MyopicDet_reducedObjective

namespace SeasonalPricing.MyopicDet

/-- Proof of Proposition 4, the special case (Aviv–Pazgal 2008, pp. 351, 359): if
`0 < ρ ≤ e^{−2+e^{−1}}`, the maximum of `(p₁ − p₂) ln(p₁)/ln(ρ) + p₂ ln(p₂)/ln(ρ)` over
`ρ ≤ p₂ ≤ p₁ ≤ 1` equals `−e^{−1+e^{−1}}/ln(ρ)`, and it is attained exactly at
`p₁* = e^{−1+e^{−1}}`, `p₂* = p₁*/e`. -/
theorem reducedObjective_special_case (ρ : ℝ) (hρ0 : 0 < ρ)
    (hρ : ρ ≤ Real.exp (-2 + Real.exp (-1))) :
    IsGreatest {g : ℝ | ∃ p1 p2 : ℝ, ρ ≤ p2 ∧ p2 ≤ p1 ∧ p1 ≤ 1 ∧ g = reducedObjective ρ p1 p2}
        (-Real.exp (-1 + Real.exp (-1)) / Real.log ρ) ∧
      ρ ≤ Real.exp (-1 + Real.exp (-1)) / Real.exp 1 ∧
      Real.exp (-1 + Real.exp (-1)) ≤ 1 ∧
      reducedObjective ρ (Real.exp (-1 + Real.exp (-1)))
          (Real.exp (-1 + Real.exp (-1)) / Real.exp 1) =
        -Real.exp (-1 + Real.exp (-1)) / Real.log ρ ∧
      ∀ p1 p2 : ℝ, ρ ≤ p2 → p2 ≤ p1 → p1 ≤ 1 →
        reducedObjective ρ p1 p2 = -Real.exp (-1 + Real.exp (-1)) / Real.log ρ →
          p1 = Real.exp (-1 + Real.exp (-1)) ∧ p2 = Real.exp (-1 + Real.exp (-1)) / Real.exp 1 := by sorry

end SeasonalPricing.MyopicDet
