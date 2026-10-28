-- Prove2me | Theorems.Thm_ValuePersPricing_Deviation_lemma_2
-- name    : ValuePersPricing.Deviation.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:26.526993+00:00
-- url     : https://prove2.me/theorems/91026912-2695-421a-829b-47448800ea75
-- title:
--   Lemma 2, p. 13 — 0 ≤ D ≤ δH and 0 ≤ δL ≤ δM ≤ δH
-- statement:
--   Let $(F,c)$ be a market with mean $\mu$, margin $M=1-c/\mu>0$, scale $S$ and coefficient of deviation $D$. Then
--   $$0\le D\le\delta_H,\qquad 0\le\delta_L\le\delta_M\le\delta_H,$$
--   where $\delta_L,\delta_M,\delta_H$ are the regime thresholds of §3.2 evaluated at $(M,S)$.
--
--   The three regimes of Theorem 2 therefore partition the whole range of possible coefficients of deviation.
--
--   Differences from the source:
--   - encoding: margin M → hypothesis c < µ (M > 0); reason: δL, δM, δH divide by M; standing assumptions as Market ν c.
-- source:
--   Elmachtoub, Gupta & Hamilton, The Value of Personalized Pricing, SSRN 3127719 (review version, PDF sha256 635e22eb…), p. 13 (PDF 13), Lemma 2; proof pp. ec3–ec4 (PDF 35–36)

import Mathlib
import Definitions.Def_ValuePersPricing_Deviation_Model

open MeasureTheory Set Filter Topology

namespace ValuePersPricing.Deviation

/-- Lemma 2 (p. 13): for a law of scale `S` and margin `M`, `0 ≤ D ≤ δ_H` and
`0 ≤ δ_L ≤ δ_M ≤ δ_H`. -/
theorem lemma_2 (ν : Measure ℝ) (c S : ℝ) (hm : Market ν c) (hc : c < mean ν)
    (hS : IsScale ν S) :
    0 ≤ coefDev ν ∧ coefDev ν ≤ deltaH (margin ν c) S ∧
    0 ≤ deltaL (margin ν c) S ∧ deltaL (margin ν c) S ≤ deltaM (margin ν c) S ∧
    deltaM (margin ν c) S ≤ deltaH (margin ν c) S := by sorry

end ValuePersPricing.Deviation
