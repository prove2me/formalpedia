-- Prove2me | Theorems.Thm_SpeedFactory_BreakEven_eq_20
-- name    : SpeedFactory.BreakEven.eq_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:57.997014+00:00
-- url     : https://prove2.me/theorems/83cda85b-7e34-4174-a92b-9331d4738924
-- title:
--   §5 (20), p. 18 — for γ ∈ (0, 1], dual sourcing beats full off-shoring iff p exceeds the break-even price p⁻
-- statement:
--   Let the demand be iid $N(\mu,\sigma)$ under the standing assumptions, and fix a smoothing parameter $\alpha\in(-1,1)$. The TBS-POUT and OUT systems may start from arbitrary deterministic initial conditions. For every allocation $\gamma\in(0,1]$,
--   $$C^{\mathrm{TBS\text{-}POUT},k^\star}(\gamma)<C^s\iff p>p^-(\gamma)=\frac{h+b}{\mu\gamma}(\sigma_i-\sigma_{i,s})\varphi[z_i]+\frac{um}{\mu\gamma}\sigma_q\varphi[z_q]+u .$$
--
--   The break-even price $p^-$ is the threshold that §5 and Proposition 4 analyse.
--
--   **Formalization Note** The break-even price divides by $\mu\gamma$, so $\gamma=0$ is excluded.
-- source:
--   Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 18, §5, (20)

import Mathlib
import Definitions.Def_SpeedFactory_BreakEven_Model
import Definitions.Def_SpeedFactory_BreakEven_Dynamics

open MeasureTheory ProbabilityTheory

namespace SpeedFactory.BreakEven

/-- The break-even price. Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 18, §5, (20).

Under iid `N(µ, σ)` demand, for every `γ ∈ (0, 1]` and smoothing `α ∈ (−1, 1)`, dual sourcing
with TBS-POUT is strictly cheaper than full off-shoring, `C^{TBS-POUT,k⋆} < C^s`, if and only if
the off-shore price exceeds the break-even price,
`p > p⁻ = (h + b)/(µγ) (σ_i − σ_{i,s})φ[z_i] + um/(µγ) σ_qφ[z_q] + u`.

**Formalization Note.** `p⁻` divides by `µγ`, so `γ = 0` is excluded. Different deterministic
initial conditions for the two systems are allowed. -/
theorem eq_20 (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Set.Ioo (-1 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d)
    (i0 j0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ) :
    ∀ γ ∈ Set.Ioc (0 : ℝ) 1,
      (costTBS M γ α i0 P d < costOUT M j0 pipe0 P d ↔ pMinus M α γ < M.p) := by sorry

end SpeedFactory.BreakEven
