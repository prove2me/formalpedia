-- Prove2me | Theorems.Thm_ValuePersPricing_Deviation_eq_EC_6
-- name    : ValuePersPricing.Deviation.eq_EC_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:30.024899+00:00
-- url     : https://prove2.me/theorems/6fd01751-d61c-4c19-98ad-1cacb88c9b82
-- title:
--   Eq. (EC.6), p. ec2 — for c = 0, µ = 1 and scale S: R_PP/R_SP ≤ log(S)/D
-- statement:
--   Let $V\sim F$ satisfy $V\ge 0$ almost surely, with mean $\mu=1$ and scale $S$, take cost $c=0$, and let $D=\mathbb E|V-1|/2$. Then
--   $$D\,\mathcal R_{PP}\le\log(S)\,\mathcal R_{SP},$$
--   which for $D>0$ is the bound $\mathcal R_{PP}/\mathcal R_{SP}\le\log(S)/D$. It coincides with the Medium Heterogeneity bound of Theorem 2 when $c=0$, $\mu=1$.
--
--   Differences from the source:
--   - generalization: (EC.6) inside the proof of Theorem 2, for F with scale S > 1 → every scale S (S ≥ 1 holds automatically); reason: the derivation uses only the first identity of Lemma 3 and the Pricing Inequality; the added case S = 1 is V = 1 a.s., where both sides are 0; for S > 1 it is the printed claim.
--   - encoding: R_PP/R_SP ≤ log(S)/D → D·R_PP ≤ log(S)·R_SP; reason: equivalent for D > 0 (R_SP > 0); at D = 0, where log(S)/D is undefined, the product form is still true; this removes only the undefined case.
-- source:
--   Elmachtoub, Gupta & Hamilton, The Value of Personalized Pricing, SSRN 3127719 (review version, PDF sha256 635e22eb…), p. ec2 (PDF 34), Eq. (EC.6)

import Mathlib
import Definitions.Def_ValuePersPricing_Deviation_Model

open MeasureTheory Set Filter Topology

namespace ValuePersPricing.Deviation

/-- Eq. (EC.6) (p. ec2), for `c = 0`, `µ = 1` and a law of scale `S`: `R_PP/R_SP ≤ log(S)/D`,
stated multiplicatively as `D · R_PP ≤ log(S) · R_SP`. -/
theorem eq_EC_6 (ν : Measure ℝ) (S : ℝ) (hm : Market ν 0) (hμ : mean ν = 1)
    (hS : IsScale ν S) :
    coefDev ν * ppProfit ν 0 ≤ Real.log S * spProfit ν 0 := by sorry

end ValuePersPricing.Deviation
