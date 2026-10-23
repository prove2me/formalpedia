-- Prove2me | Theorems.Thm_SpeedFactory_BreakEven_proposition_3
-- name    : SpeedFactory.BreakEven.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:57.8561+00:00
-- url     : https://prove2.me/theorems/6c84cb0d-47b0-4429-b7f8-55e9dc29d72e
-- title:
--   Proposition 3 (Bang-bang), p. 11 — the optimal SpeedFactory allocation is γ⋆ = 0 if u > p and γ⋆ = 1 if u < p
-- statement:
--   Let the demand be iid $N(\mu,\sigma)$ under the standing assumptions, and fix a smoothing parameter $\alpha\in(-1,1)$. Let $C^{\mathrm{TBS\text{-}POUT},k^\star}(\gamma)$ be the optimized long-run cost of TBS-POUT at allocation $\gamma$. Then:
--
--   1. if $u>p$, then $C^{\mathrm{TBS\text{-}POUT},k^\star}(0)<C^{\mathrm{TBS\text{-}POUT},k^\star}(\gamma)$ for every $\gamma\in(0,1]$, so $\gamma^\star=0$;
--   2. if $u<p$, then $C^{\mathrm{TBS\text{-}POUT},k^\star}(1)<C^{\mathrm{TBS\text{-}POUT},k^\star}(\gamma)$ for every $\gamma\in[0,1)$, so $\gamma^\star=1$.
--
--   The optimal strategic allocation is therefore a boundary solution.
--
--   **Formalization Note** "Optimal" is read as the unique minimizer over $[0,1]$. The knife-edge case $u=p$ is excluded, as in the paper.
-- source:
--   Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 11, Proposition 3

import Mathlib
import Definitions.Def_SpeedFactory_BreakEven_Model
import Definitions.Def_SpeedFactory_BreakEven_Dynamics

open MeasureTheory ProbabilityTheory

namespace SpeedFactory.BreakEven

/-- Proposition 3 (Bang-bang). Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 11, Proposition 3.

Under iid `N(µ, σ)` demand and TBS-POUT with a fixed smoothing `α ∈ (−1, 1)`, the optimized
cost `C^{TBS-POUT,k⋆}(γ)` over `γ ∈ [0, 1]` has the unique minimizer `γ⋆ = 0` if `u > p` and
`γ⋆ = 1` if `u < p`.

**Formalization Note.** "Optimal" is read as the unique minimizer over `[0, 1]`; the knife-edge
`u = p` is excluded, as printed. iid demand, `m > 1`, `α ∈ (−1, 1)`, expected Cesàro (5). -/
theorem proposition_3 (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Set.Ioo (-1 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d) (i0 : ℝ) :
    (M.p < M.u → ∀ γ ∈ Set.Ioc (0 : ℝ) 1, costTBS M 0 α i0 P d < costTBS M γ α i0 P d) ∧
    (M.u < M.p → ∀ γ ∈ Set.Ico (0 : ℝ) 1,
      costTBS M 1 α i0 P d < costTBS M γ α i0 P d) := by sorry

end SpeedFactory.BreakEven
