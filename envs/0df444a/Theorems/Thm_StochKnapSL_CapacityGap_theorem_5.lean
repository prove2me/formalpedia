-- Prove2me | Theorems.Thm_StochKnapSL_CapacityGap_theorem_5
-- name    : StochKnapSL.CapacityGap.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:41.694856+00:00
-- url     : https://prove2.me/theorems/bbeef375-fe74-4947-b608-7fd8beee158d
-- title:
--   Theorem 5, p. 18 — with independent demands bounded by Δ, Q^Anti_I − Q^Adap_I ≤ 2Δ
-- statement:
--   Let $N$ customers have independent, positive random demands $\tilde d_1, \dots, \tilde d_N$, all almost surely at most a constant $\Delta > 0$, and Type-I service targets $\alpha_i \in [0,1]$: customer $i$ must be fully served with probability at least $\alpha_i$. Let $Q^{\mathrm{Anti}}_I$ be the least capacity with which a randomized anticipative policy meets all targets, and $Q^{\mathrm{Adap}}_I$ the least capacity with which a randomized adaptive policy does. An anticipative policy fixes a priority order before demands are seen. An adaptive policy picks the next customer after seeing the demands already served. Then
--   $$ Q^{\mathrm{Anti}}_I - Q^{\mathrm{Adap}}_I \le 2\Delta. $$
--
--   The bound does not depend on the number of customers. Seeing demands as they are revealed saves at most two maximal demands of capacity.
--
--   **Formalization Note.** Both optimal capacities are real infima over non-empty sets: under the standing assumptions $Q = N\Delta$ is feasible for both classes.
-- source:
--   Lyu, Chou, Teo, Zheng & Zhong, Stochastic Knapsack Revisited: The Service Level Perspective, SSRN working paper 3674463 (version of 2021-05-29), p. 18, Theorem 5

import Mathlib
import Definitions.Def_StochKnapSL_CapacityGap_Model
open MeasureTheory ProbabilityTheory

namespace StochKnapSL.CapacityGap

/-- Theorem 5, p. 18: `Q^Anti_I − Q^Adap_I ≤ 2Δ`. -/
theorem theorem_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {N : ℕ} (d : Fin N → Ω → ℝ) (Δ : ℝ) (α : Fin N → ℝ)
    (hS : Standing μ d Δ α) :
    QAnti μ d α - QAdap μ d α ≤ 2 * Δ := by sorry

end StochKnapSL.CapacityGap
