-- Prove2me | Theorems.Thm_StochKnapSL_CapacityGap_theorem_4
-- name    : StochKnapSL.CapacityGap.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:18.86948+00:00
-- url     : https://prove2.me/theorems/ef73ce03-813e-4ffd-9346-5483ce8e40eb
-- title:
--   Theorem 4, p. 18 — the optimal adaptive Type-I capacity is at least Q_II − Δ
-- statement:
--   Under the standing assumptions of §3.3, the optimal capacity that randomized adaptive policies need to fully serve each customer $i$ with probability at least $\alpha_i$ satisfies
--   $$ Q^{\mathrm{Adap}}_I \ge Q_{II} - \Delta. $$
--
--   This is the lower half of the capacity-gap result (Theorem 5).
-- source:
--   Lyu, Chou, Teo, Zheng & Zhong, Stochastic Knapsack Revisited: The Service Level Perspective, SSRN working paper 3674463 (version of 2021-05-29), p. 18, Theorem 4 (proof in Appendix A.3, p. 37)

import Mathlib
import Definitions.Def_StochKnapSL_CapacityGap_Model
open MeasureTheory ProbabilityTheory

namespace StochKnapSL.CapacityGap

/-- Theorem 4, p. 18: `Q^Adap_I ≥ Q_II − Δ`. -/
theorem theorem_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (d : Fin N → Ω → ℝ) (Δ : ℝ) (α : Fin N → ℝ)
    (hS : Standing μ d Δ α) :
    QII μ d α - Δ ≤ QAdap μ d α := by sorry

end StochKnapSL.CapacityGap
