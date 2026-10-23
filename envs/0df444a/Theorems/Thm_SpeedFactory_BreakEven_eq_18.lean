-- Prove2me | Theorems.Thm_SpeedFactory_BreakEven_eq_18
-- name    : SpeedFactory.BreakEven.eq_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:00.475506+00:00
-- url     : https://prove2.me/theorems/906310a9-2ac9-4d89-b643-bcb93b1c7797
-- title:
--   §3 (18), p. 11 — the single-sourcing OUT benchmark C^s = σ_{i,s}(h + b)φ[z_i] + pµ with σ_{i,s} = σ√L
-- statement:
--   Let the demand be iid $N(\mu,\sigma)$ under the standing assumptions. Consider single off-shore sourcing with the order-up-to policy (75), target $i^\star$, and deterministic initial inventory and outstanding orders. Then:
--
--   1. for every target $i^\star$ and every period $t\ge L$, the inventory variance is exactly $\operatorname{Var}(i_t)=L\sigma^2=\sigma_{i,s}^2$, see (70);
--   2. the long-run average cost, as a function of $i^\star$, has the unique minimizer $i^\star=\sigma_{i,s}z_i$ and the minimum value
--   $$C^s=\sigma_{i,s}(h+b)\varphi[z_i]+p\mu,\qquad \sigma_{i,s}=\sigma\sqrt L. \qquad (18)$$
--
--   $C^s$ is the full off-shoring benchmark against which the SpeedFactory is compared in §5.
--
--   **Formalization Note** $C^s$ is the optimized cost of the OUT policy. The paper's accompanying assertion that a traditional OUT policy is optimal among all single-sourcing policies is not formalized. Long-run averages are taken of expected period costs.
-- source:
--   Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 11, §3, (18); p. 35, (70)

import Mathlib
import Definitions.Def_SpeedFactory_BreakEven_Model
import Definitions.Def_SpeedFactory_BreakEven_Dynamics

open MeasureTheory ProbabilityTheory

namespace SpeedFactory.BreakEven

/-- The single-sourcing benchmark cost. Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 11, §3, (18); the variance (70), p. 35.

Under iid `N(µ, σ)` demand, single off-shore sourcing with the order-up-to policy (75) has, for
every target `i⋆`, inventory variance exactly `Lσ² = σ²_{i,s}` from period `L` on (70), and its
long-run cost is minimized over `i⋆` exactly at `i⋆ = σ_{i,s} z_i`, with minimum
`C^s = σ_{i,s}(h + b)φ[z_i] + pµ`, `σ_{i,s} = σ√L` (18).

**Formalization Note.** `C^s` is the optimized OUT-policy cost; the sentence's claim that the
OUT policy is optimal among all single-sourcing policies is not formalized. The initial inventory
and pipeline are deterministic and arbitrary; expected Cesàro reading of (5). -/
theorem eq_18 (M : Model) (hM : M.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d) (i0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ) :
    let Cs := sigmaIS M * (M.h + M.b) * stdNormalPDF (zi M) + M.p * M.μ
    IsLeast (Set.range fun s : ℝ => lrCostOUT M s i0 pipe0 P d) Cs ∧
    lrCostOUT M (sigmaIS M * zi M) i0 pipe0 P d = Cs ∧
    (∀ s : ℝ, lrCostOUT M s i0 pipe0 P d = Cs → s = sigmaIS M * zi M) ∧
    ∀ (iStar : ℝ) (t : ℕ), M.L ≤ t →
      variance (invOUT M iStar i0 pipe0 d t) P = M.L * M.σ ^ 2 := by sorry

end SpeedFactory.BreakEven
