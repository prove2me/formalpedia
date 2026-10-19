-- Prove2me | Theorems.Thm_RightRepair_Equilibrium_G41_profit_gaps
-- name    : RightRepair.Equilibrium.G41_profit_gaps
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:13:48.900979+00:00
-- url     : https://prove2.me/theorems/d5469baa-e943-4047-a971-721759cc1922
-- title:
--   (G.41), OA p. 23 — profit gaps between three reduced problems
-- statement:
--   Let $\pi_5$ be the extended partial-repair objective at $p_{n5}=(c+1+\delta(1-f))/2$ and $p_{r5}=(\delta+c_M)/2$. Let $\pi_4$ and $\pi_1$ be the optimal values of the full-repair and no-repair reduced problems. Their two differences equal the nonnegative squared expressions in (G.41):
--
--   $$
--   \pi_5-\pi_4=\frac{(c_M+\delta-2c\delta+3c_M\delta-\delta^2-2c_M\delta f)^2}{4\delta(1-\delta)(1+3\delta)}\ge0,
--   $$
--
--   $$
--   \pi_5-\pi_1=\frac{(c_M+\delta-2c\delta+3c_M\delta-\delta f+\delta^2f-\delta^2+c\delta f-4c_M\delta f+c_M\delta f^2)^2}{4\delta(1-\delta)[1+\delta(1-f)(3-f)]}\ge0.
--   $$
--
--   These identities compare the candidate profits. Their algebraic form remains valid beyond the interior-feasibility regime used for the paper's economic comparison.
--
--   **Formalization Note** The source omits a factor $\delta$ from the second printed denominator; direct substitution into (G.36) gives the corrected denominator shown here. The polynomial extension of $\pi_5$ avoids a $0/0$ artifact where its rational expression is undefined. Standing assumptions contain the nonnegative unit-cost pins.
-- source:
--   Jin, Yang & Zhu, Right to Repair: Pricing, Welfare, and Environmental Implications, authors' manuscript of Management Science (2022), doi:10.1287/mnsc.2022.4401 (PDF sha256 b869b33a…1763), OA pp. 21–23, (G.36), (G.38)–(G.41) (PDF 54–56)

import Mathlib
import Definitions.Def_RightRepair_Equilibrium_Setting

namespace RightRepair.Equilibrium

theorem G41_profit_gaps (P : Params) (hP : Standing P) :
    let π₅ := profit5 P (pnNo P) ((P.δ + P.cM) / 2)
    let π₄ := (P.c - P.δ + P.cM * P.f - 1) ^ 2 / (4 * (1 + 3 * P.δ))
    let π₁ := (P.c - P.δ + P.δ * P.f - 1) ^ 2 /
      (4 * (P.δ * P.f ^ 2 - 4 * P.δ * P.f + 3 * P.δ + 1))
    π₅ - π₄ =
      (P.cM + P.δ - 2 * P.c * P.δ + 3 * P.cM * P.δ - P.δ ^ 2 -
        2 * P.cM * P.δ * P.f) ^ 2 /
        (4 * P.δ * (1 - P.δ) * (1 + 3 * P.δ)) ∧
    π₅ - π₁ =
      (P.cM + P.δ - 2 * P.c * P.δ + 3 * P.cM * P.δ -
        P.δ * P.f + P.δ ^ 2 * P.f - P.δ ^ 2 + P.c * P.δ * P.f -
        4 * P.cM * P.δ * P.f + P.cM * P.δ * P.f ^ 2) ^ 2 /
        (4 * P.δ * (1 - P.δ) *
          (1 + P.δ * (1 - P.f) * (3 - P.f))) ∧
    0 ≤ π₅ - π₄ ∧ 0 ≤ π₅ - π₁ := by sorry

end RightRepair.Equilibrium
