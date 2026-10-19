-- Prove2me | Theorems.Thm_SpeedFactory_BreakEven_eq_19
-- name    : SpeedFactory.BreakEven.eq_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:57.474497+00:00
-- url     : https://prove2.me/theorems/1a858d28-4cc7-4c2a-99ea-1de509474e04
-- title:
--   §5 (19), p. 17 — C^{TBS-POUT,k⋆} − C^s = (h + b)(σ_i − σ_{i,s})φ[z_i] + umσ_qφ[z_q] + µγ(u − p)
-- statement:
--   Let the demand be iid $N(\mu,\sigma)$ under the standing assumptions, and fix a smoothing parameter $\alpha\in(-1,1)$. The TBS-POUT and OUT systems may start from arbitrary deterministic initial conditions. For every $\gamma\in[0,1]$, the optimized dual-sourcing cost and the single-sourcing benchmark satisfy
--   $$C^{\mathrm{TBS\text{-}POUT},k^\star}-C^s=(h+b)(\sigma_i-\sigma_{i,s})\varphi[z_i]+um\sigma_q\varphi[z_q]+\mu\gamma(u-p).$$
--
--   The sign of this difference decides when a SpeedFactory is economical.
--
--   **Formalization Note** Both costs are the optimized long-run expected costs of the model's dynamics, so this is a statement about the model and not an identity between the closed forms (13) and (18).
-- source:
--   Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 17, §5, (19)

import Mathlib
import Definitions.Def_SpeedFactory_BreakEven_Model
import Definitions.Def_SpeedFactory_BreakEven_Dynamics

open MeasureTheory ProbabilityTheory

namespace SpeedFactory.BreakEven

/-- The cost difference between dual sourcing and full off-shoring.
Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 17, §5, (19).

Under iid `N(µ, σ)` demand, for every `γ ∈ [0, 1]` and smoothing `α ∈ (−1, 1)`,
`C^{TBS-POUT,k⋆} − C^s = (h + b)(σ_i − σ_{i,s})φ[z_i] + umσ_qφ[z_q] + µγ(u − p)`, where both costs
are the optimized long-run costs of the model.

**Formalization Note.** The TBS-POUT and OUT systems may start from different deterministic
initial inventories (`i0`, `j0`) and the OUT system from any deterministic pipeline; the long-run
costs do not depend on them. -/
theorem eq_19 (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Set.Ioo (-1 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d)
    (i0 j0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ) :
    ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      costTBS M γ α i0 P d - costOUT M j0 pipe0 P d
        = (M.h + M.b) * (sigmaI M α - sigmaIS M) * stdNormalPDF (zi M)
          + M.u * M.m * sigmaQ M α * stdNormalPDF (zq M) + M.μ * γ * (M.u - M.p) := by sorry

end SpeedFactory.BreakEven
