-- Prove2me | Theorems.Thm_StochLoadBal_Makespan_observation_3
-- name    : StochLoadBal.Makespan.observation_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:00.028199+00:00
-- url     : https://prove2.me/theorems/31589011-619f-4fc2-a96c-af58e145cc36
-- title:
--   Observation 3 — per-machine tail Pr[Σ_{j∈J_i} X′_ij > b + 1 + α] ≤ ℓ_i^(−α)
-- statement:
--   Let $m\ge1$, let the sizes $X_{ij}\ge0$ be measurable and integrable with the jobs independent, let $y$ be a feasible solution of the LP (5)–(9) with parameter $b$, and let $\sigma$ be an assignment with properties (13)–(14), with job sets $J_i$ and machine classes $\ell_i$. Then for every machine $i$ and every $\alpha\ge0$,
--   $$\Pr\Big[\sum_{j\in J_i}X'_{ij}\ >\ b+1+\alpha\Big]\ \le\ \ell_i^{-\alpha}.$$
--
--   Machines of a high class have rapidly decaying truncated loads; Lemma 7 sums these bounds over the machines of class at least $3$.
--
--   **Formalization Note** LP feasibility is assumed so that every class satisfies $\ell_i\ge1$ (Observation 1); with the junk class $0$ the right side would be $0$. Only the independence of the jobs on machine $i$ is used, which follows from the independence of the jobs.
-- source:
--   Gupta, Kumar, Nagarajan & Shen, Stochastic Load Balancing on Unrelated Machines, arXiv:1904.07271v1, p. 13, Observation 3

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Rounding

namespace StochLoadBal.Makespan

open MeasureTheory ProbabilityTheory

/-- Observation 3 (p. 13): for a feasible LP solution `y` and an assignment `σ` with
(13)–(14), every machine `i` of class `ℓ_i` satisfies
`Pr[Σ_{j ∈ J_i} X'_{ij} > b + 1 + α] ≤ ℓ_i^{-α}` for all `α ≥ 0`. -/
theorem observation_3 {m n : ℕ} (hm : 1 ≤ m) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin m → Fin n → Ω → ℝ)
    (hmeas : ∀ i j, Measurable (X i j)) (hnn : ∀ i j ω, 0 ≤ X i j ω)
    (hint : ∀ i j, Integrable (X i j) P) (hind : iIndepFun (fun j ω i => X i j ω) P)
    (b : ℝ) (y : Fin m → Fin n → ℝ) (hy : LPFeasible P X b y)
    (σ : Fin n → Fin m) (hσ : IsRoundingOutput P X b y σ) (i : Fin m) (α : ℝ) (hα : 0 ≤ α) :
    (P {ω | b + 1 + α < ∑ j ∈ Finset.univ.filter (fun j => σ j = i), trunc (X i j ω)}).toReal
      ≤ (machineClass P X b y i : ℝ) ^ (-α) := by sorry

end StochLoadBal.Makespan
