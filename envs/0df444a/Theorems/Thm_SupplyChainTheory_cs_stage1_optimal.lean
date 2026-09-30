-- Prove2me | Theorems.Thm_SupplyChainTheory_cs_stage1_optimal
-- name    : SupplyChainTheory.cs_stage1_optimal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:18:11.185573+00:00
-- url     : https://prove2.me/theorems/d77f018f-2b89-4a7d-b8b4-78914e0673e7
-- title:
--   Eq. (6.30): $S^*_1 = F_1^{-1}\big((p + h'_2)/(h_1 + p + h'_2)\big)$
-- statement:
--   At stage 1, with $h_1 > 0$, $p > 0$ and a lead-time demand $D_1$ of finite mean whose
--   distribution function $F_1$ is continuous, every minimizer $S^*_1$ of $g_1$ satisfies the
--   critical-fractile equation
--
--   $$ F_1(S^*_1) \;=\; \frac{p + h'_2}{h_1 + p + h'_2} \;=\; \frac{p + \sum_{i=2}^N h_i}{p + \sum_{i=1}^N h_i}. $$
--
--   This is (4.17) applied to the newsvendor form (6.29) of $g_1$: its derivative is
--   $(h_1 + p + h'_2) F_1(y) - (p + h'_2)$, which vanishes at the minimizer. The book writes the
--   minimizer as $F_1^{-1}$ of the fractile; the equation form is what a continuous $F_1$
--   supports without a choice of inverse.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 196, Sect. 6.2.2, Eq. (6.30)

import Definitions.Def_SupplyChainTheory_multiechelon

namespace SupplyChainTheory

theorem cs_stage1_optimal (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ)
    (S : ℕ → ℝ) (hN : 1 ≤ N) [MeasureTheory.IsProbabilityMeasure (D 1)]
    [MeasureTheory.NullSingletonClass (D 1)]
    (hD : MeasureTheory.Integrable (fun x => x) (D 1)) (hh : 0 < h 1) (hp : 0 < p)
    (hmin : ∀ y, csG N h p D S 1 (S 1) ≤ csG N h p D S 1 y) :
    ProbabilityTheory.cdf (D 1) (S 1)
      = (p + localHolding N h 2) / (h 1 + p + localHolding N h 2) := by sorry

end SupplyChainTheory
