-- Prove2me | Theorems.Thm_ValuePersPricing_Deviation_lemma_EC_1
-- name    : ValuePersPricing.Deviation.lemma_EC_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:00.32646+00:00
-- url     : https://prove2.me/theorems/db440120-4d06-490d-90ff-487f55aa454e
-- title:
--   Lemma EC.1, p. ec3 — for c = 0, µ = 1 and D > δM: R_PP/R_SP ≤ −W₋₁(−1/(eS(1 − D)))
-- statement:
--   Let $V\sim F$ satisfy $V\ge 0$ almost surely, with mean $\mu=1$ and scale $S$, take cost $c=0$, and let $D=\mathbb E|V-1|/2$. If $D>\delta_M=\log S/(1+\log S)$ (the threshold at $M=1$), then
--   $$\mathcal R_{PP}\le -W_{-1}\Big(\frac{-1}{eS(1-D)}\Big)\,\mathcal R_{SP}.\qquad\text{(EC.7)}$$
--
--   This is the High Heterogeneity bound of Theorem 2 in the standardized case $c=0$, $\mu=1$.
--
--   **Formalization Note** Under the hypotheses $S>1$ and $S(1-D)\ge 1$ (Lemma 2), so the argument of $W_{-1}$ lies in $[-1/e,0)$.
--
--   Differences from the source:
--   - encoding: R_PP/R_SP ≤ B → R_PP ≤ B·R_SP; reason: R_SP > 0 under the hypotheses; avoids division junk.
-- source:
--   Elmachtoub, Gupta & Hamilton, The Value of Personalized Pricing, SSRN 3127719 (review version, PDF sha256 635e22eb…), p. ec3 (PDF 35), Lemma EC.1, Eq. (EC.7); proof pp. ec5–ec6 (PDF 37–38)

import Mathlib
import Definitions.Def_ValuePersPricing_Deviation_Model

open MeasureTheory Set Filter Topology

namespace ValuePersPricing.Deviation

/-- Lemma EC.1 (p. ec3), Eq. (EC.7): for `c = 0`, `µ = 1`, a law of scale `S` and `D > δ_M`,
`R_PP/R_SP ≤ −W₋₁(−1/(e S (1 − D)))`, stated multiplicatively. -/
theorem lemma_EC_1 (ν : Measure ℝ) (S : ℝ) (hm : Market ν 0) (hμ : mean ν = 1)
    (hS : IsScale ν S) (hD : deltaM 1 S < coefDev ν) :
    ppProfit ν 0 ≤
      -lambertWm1 (-1 / (Real.exp 1 * S * (1 - coefDev ν))) * spProfit ν 0 := by sorry

end ValuePersPricing.Deviation
