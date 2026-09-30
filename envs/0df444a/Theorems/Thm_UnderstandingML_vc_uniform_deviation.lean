-- Prove2me | Theorems.Thm_UnderstandingML_vc_uniform_deviation
-- name    : UnderstandingML.vc_uniform_deviation
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:54:07.672988+00:00
-- url     : https://prove2.me/theorems/68f00474-63f5-443d-80e4-0ca5b7cbc766
-- title:
--   §28.1: for VCdim(H) = d, w.p. ≥ 1−δ every h ∈ H has |L_D(h) − L_S(h)| ≤ 2√((8d log(em/d) + 2 log(4/δ))/m)
-- statement:
--   **§28.1 (p. 393).** Using Theorem 26.5 we obtain that with probability of at least $1 - \delta$, for every $h \in H$, $L_D(h) - L_S(h) \le \sqrt{8d\log(em/d)/m} + \sqrt{2\log(2/\delta)/m}$. Repeating the argument for minus the zero-one loss and applying the union bound, with probability of at least $1 - \delta$, for every $h \in H$,
--   $$|L_D(h) - L_S(h)| \le \sqrt{\frac{8d\log(em/d)}{m}} + \sqrt{\frac{2\log(4/\delta)}{m}} \le 2\sqrt{\frac{8d\log(em/d) + 2\log(4/\delta)}{m}}.$$
--
--   Formally: for $m > d + 1$. $H$ consists of measurable hypotheses with the countable-approximation property of Mission IV (Remark 3.1).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §28.1 p. 393, the two-sided uniform deviation bound from Theorem 26.5

import Definitions.Def_UnderstandingML_FundamentalProof

open MeasureTheory

namespace UnderstandingML

/-- **§28.1** (p. 393). Using Theorem 26.5 for the 0–1 loss and for minus the 0–1 loss and the
union bound: with probability of at least `1 − δ`, for every `h ∈ H`,
`|L_D(h) − L_S(h)| ≤ √(8d log(em/d)/m) + √(2 log(4/δ)/m) ≤ 2 √((8d log(em/d) + 2 log(4/δ))/m)`.
Measurable `H` with the countable-approximation property (Remark 3.1), `m > d + 1`. -/
theorem vc_uniform_deviation {X : Type*} [MeasurableSpace X] (H : Set (X → Bool))
    (hH : ∀ h ∈ H, Measurable h) (hsep : PointwiseSeparable H) (d : ℕ) (hd : vcDim H = d)
    (D : Measure (X × Bool)) [IsProbabilityMeasure D] (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : d + 1 < m) :
    iidLaw D m {S | ∃ h ∈ H,
      2 * Real.sqrt ((8 * d * Real.log (Real.exp 1 * m / d) + 2 * Real.log (4 / δ)) / m) <
        |risk loss01 D h - empRisk loss01 S h|} ≤ ENNReal.ofReal δ := by sorry

end UnderstandingML
