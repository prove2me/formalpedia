-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P02_smallThermalNoiseExpansion
-- name    : QAlgorithms.Papers.Independent.Intake100.P02.smallThermalNoiseExpansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:49:55.950085+00:00
-- url     : https://prove2.me/theorems/1f754711-0b33-4abe-97cd-df17f3874711
-- title:
--   Joint high-loss and small-thermal-noise expansion
-- statement:
--   Let $R_{\rm LB}(\eta,\omega)=-\log_2(1-\eta)-s(\omega)$, with $s$ the single-mode entropy in bits under vacuum variance $1/2$, and set $\omega=\bar n+1/2$. As $\eta\downarrow0$ and $\bar n\downarrow0$ jointly through $0<\eta<1$, $\bar n\ge0$,
--
--   $$R_{\rm LB}(\eta,\bar n+1/2)=(\eta-\bar n)\log_2 e+\bar n\log_2\bar n+o(\eta+\bar n).$$
--
--   The term $0\log_2 0$ is zero. Explicitly, for every $\epsilon>0$ there is $0<\delta<1$ such that the absolute remainder is at most $\epsilon(\eta+\bar n)$ whenever $0<\eta<\delta$ and $0\le\bar n<\delta$. The same $\delta$ works throughout that parameter rectangle.
--
--   This records the leading signed rate in the high-loss, low-thermal-occupation regime. The printed descriptions “low loss” and “omega approximately 1” are corrected to high loss and $\omega\to1/2$; the displayed leading expression is unchanged.
-- source:
--   Theory of channel simulation and bounds for private communication, arXiv:1711.09909v3, PDF p. 15, Remark 9, Eq. (118): small-transmissivity, small-noise expansion

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P02

open Filter MeasureTheory QAlgorithms

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal)

/-- arXiv:1711.09909v3, PDF p.15, (118): joint leading expansion of (110).
Printed: "low loss eta approximately 0" and "omega approximately 1".
Changed: high loss eta -> 0, omega=nbar+1/2 -> 1/2.
Why: (108),(110),(111) and nbar -> 0 force these conventions. The displayed
leading expression is unchanged. Independent moderation is required.
The remainder is o(eta+nbar) in the physical nonnegative-noise quadrant. -/
theorem smallThermalNoiseExpansion :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧ delta < 1 ∧
      ∀ eta nbar : ℝ, 0 < eta → eta < delta → 0 ≤ nbar → nbar < delta →
        |reverseRateExpression eta (nbar + 1 / 2) - leadingRateExpression eta nbar| ≤
          eps * (eta + nbar) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P02

end
