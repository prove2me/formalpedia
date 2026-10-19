-- Prove2me | Theorems.Thm_SpeedFactory_BreakEven_proposition_4
-- name    : SpeedFactory.BreakEven.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:59.512151+00:00
-- url     : https://prove2.me/theorems/a5422af9-63fb-4d6e-b852-36b8f69fa2d0
-- title:
--   Proposition 4, pp. 18–19 — under (21) p⁻ is concave in γ and dual sourcing beats off-shoring for p⁻ < p < u; otherwise p⁻ is convex and γ = 1 is optimal for p > p⁻
-- statement:
--   Let the demand be iid $N(\mu,\sigma)$ under the standing assumptions, and dual source with a linear TBS-POUT policy at a fixed smoothing parameter $\alpha\in(-1,1)$. Let $p^-(\gamma)$ be the break-even price (20) on $\gamma\in(0,1]$. Let $C^{\mathrm{TBS\text{-}POUT},k^\star}(\gamma)$ be the optimized dual-sourcing cost and $C^s$ the optimized single off-shore sourcing cost, each started from arbitrary deterministic initial conditions.
--
--   1. If
--   $$\frac{h+b}{um}\cdot\frac{\sigma_{i,s}-\sigma_i}{\sigma_q}\cdot\frac{\varphi[z_i]}{\varphi[z_q]}>1, \qquad (21)$$
--   then $p^-$ is concave on $(0,1]$, and dual sourcing dominates single off-shoring when $p^-<p<u$: for every $\gamma\in(0,1]$ with $p^-(\gamma)<p<u$, $C^{\mathrm{TBS\text{-}POUT},k^\star}(\gamma)<C^s$.
--   2. Otherwise, $p^-$ is convex on $(0,1]$, and complete re-shoring is optimal when $p>p^-$. That is, if $p>p^-(\gamma)$ for some $\gamma\in(0,1]$, then $\gamma=1$ is the unique minimizer of $C^{\mathrm{TBS\text{-}POUT},k^\star}$ over $[0,1]$ and $C^{\mathrm{TBS\text{-}POUT},k^\star}(1)<C^s$.
--
--   This is the paper's strategic prescription: when (21) holds, a SpeedFactory that serves only the demand variability can beat full off-shoring even when local production costs more than off-shore purchasing.
--
--   **Formalization Note** Both costs are defined from the inventory dynamics and minimized over safety stock and capacity, not by the closed forms (13) and (18). The printed "if" is kept as an implication, and "Otherwise" is read as "if (21) fails". The break-even price is considered for $\gamma\in(0,1]$ only, since it divides by $\mu\gamma$.
-- source:
--   Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), pp. 18–19, Proposition 4, (21)

import Mathlib
import Definitions.Def_SpeedFactory_BreakEven_Model
import Definitions.Def_SpeedFactory_BreakEven_Dynamics

open MeasureTheory ProbabilityTheory

namespace SpeedFactory.BreakEven

/-- Proposition 4 (`p⁻` concavity). Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), pp. 18–19, Proposition 4, (21).

Let the demand be iid `N(µ, σ)` and dual source with TBS-POUT at smoothing `α ∈ (−1, 1)`.
* If condition (21) holds, the break-even price `p⁻(γ)` of (20) is concave in `γ ∈ (0, 1]`, and
  dual sourcing dominates single off-shoring when `p⁻ < p < u`: for every `γ ∈ (0, 1]` with
  `p⁻(γ) < p < u`, `C^{TBS-POUT,k⋆}(γ) < C^s`.
* Otherwise `p⁻` is convex in `γ ∈ (0, 1]`, and complete re-shoring is optimal when `p > p⁻`: for
  every `γ ∈ (0, 1]` with `p > p⁻(γ)`, `γ = 1` is the unique minimizer of `C^{TBS-POUT,k⋆}`
  over `[0, 1]` and `C^{TBS-POUT,k⋆}(1) < C^s`.

**Formalization Note.** `C^{TBS-POUT,k⋆}` and `C^s` are the optimized long-run expected costs
of the TBS-POUT and OUT dynamics (not the closed forms (13), (18)). iid demand, `m > 1`,
`α ∈ (−1, 1)`, `γ ∈ (0, 1]` for `p⁻` (it divides by `µγ`). The printed "if" is kept as an
implication; "Otherwise" is read as "if (21) fails". The two systems may start from different
deterministic initial conditions. -/
theorem proposition_4 (M : Model) (hM : M.Standing) {α : ℝ} (hα : α ∈ Set.Ioo (-1 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d)
    (i0 j0 : ℝ) (pipe0 : Fin (M.L - 1) → ℝ) :
    (Cond21 M α →
      ConcaveOn ℝ (Set.Ioc (0 : ℝ) 1) (pMinus M α) ∧
      ∀ γ ∈ Set.Ioc (0 : ℝ) 1, pMinus M α γ < M.p → M.p < M.u →
        costTBS M γ α i0 P d < costOUT M j0 pipe0 P d) ∧
    (¬ Cond21 M α →
      ConvexOn ℝ (Set.Ioc (0 : ℝ) 1) (pMinus M α) ∧
      ∀ γ ∈ Set.Ioc (0 : ℝ) 1, pMinus M α γ < M.p →
        (∀ γ' ∈ Set.Ico (0 : ℝ) 1, costTBS M 1 α i0 P d < costTBS M γ' α i0 P d) ∧
        costTBS M 1 α i0 P d < costOUT M j0 pipe0 P d) := by sorry

end SpeedFactory.BreakEven
