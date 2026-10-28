-- Prove2me | Theorems.Thm_ValuePersPricing_Deviation_eq_EC_5
-- name    : ValuePersPricing.Deviation.eq_EC_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:28.453154+00:00
-- url     : https://prove2.me/theorems/35fa7cb6-5712-419e-b60a-7258c4cf4ba2
-- title:
--   Eq. (EC.5), p. ec2 — for c = 0, µ = 1 and all D: R_PP/R_SP ≤ W₋₁((D−1)/e)/(D−1)
-- statement:
--   Let $V\sim F$ satisfy $V\ge 0$ almost surely with mean $\mu=1$, take cost $c=0$, and let $D=\mathbb E|V-1|/2$. Then
--   $$\mathcal R_{PP}\le\frac{W_{-1}\big(\frac{D-1}{e}\big)}{D-1}\,\mathcal R_{SP}.$$
--   No assumption on the scale is made: the bound holds for every such law, bounded or not. It coincides with the Low Heterogeneity bound of Theorem 2 when $c=0$, $\mu=1$.
--
--   **Formalization Note** $D<1$ always holds here, so the division is genuine and the argument of $W_{-1}$ lies in $[-1/e,0)$.
--
--   Differences from the source:
--   - generalization: (EC.5) inside the proof of Theorem 2, for F with scale S > 1 (S possibly infinite, p. 8) → every law with c = 0, µ = 1, with no scale hypothesis; reason: the derivation (EC.2)–(EC.5) uses only the second identity of Lemma 3 and the Pricing Inequality, neither of which involves S; the added case S = 1 is V = 1 a.s., where the bound is 1 = R_PP/R_SP; for scale S > 1 it is the printed claim.
--   - encoding: R_PP/R_SP ≤ B → R_PP ≤ B·R_SP; reason: R_SP > 0 under the hypotheses, and the product form cannot hold vacuously through a zero denominator.
-- source:
--   Elmachtoub, Gupta & Hamilton, The Value of Personalized Pricing, SSRN 3127719 (review version, PDF sha256 635e22eb…), p. ec2 (PDF 34), Eq. (EC.5)

import Mathlib
import Definitions.Def_ValuePersPricing_Deviation_Model

open MeasureTheory Set Filter Topology

namespace ValuePersPricing.Deviation

/-- Eq. (EC.5) (p. ec2), for `c = 0`, `µ = 1` and every law (no scale hypothesis):
`R_PP/R_SP ≤ W₋₁((D − 1)/e)/(D − 1)`, stated multiplicatively. -/
theorem eq_EC_5 (ν : Measure ℝ) (hm : Market ν 0) (hμ : mean ν = 1) :
    ppProfit ν 0 ≤
      lambertWm1 ((coefDev ν - 1) / Real.exp 1) / (coefDev ν - 1) * spProfit ν 0 := by sorry

end ValuePersPricing.Deviation
