-- Prove2me | Theorems.Thm_SpeedFactory_BreakEven_proposition_1
-- name    : SpeedFactory.BreakEven.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:52.303922+00:00
-- url     : https://prove2.me/theorems/355e3ecf-babe-4ade-be42-6a4c6d311827
-- title:
--   Proposition 1, p. 9 — optimal safety stock i⋆ = σ_i z_i and capacity k⋆ = µγ + σ_q z_q, and the minimal long-run TBS-POUT cost (13)
-- statement:
--   Let the demand be iid $N(\mu,\sigma)$ under the standing assumptions. Consider TBS-POUT with allocation $\gamma\in[0,1]$ and smoothing $\alpha\in(-1,1)$, from any deterministic initial inventory. Write $\sigma_i,\sigma_q$ for the standard deviations (14) and $z_i=\Phi^{-1}[b/(b+h)]$, $z_q=\Phi^{-1}[(m-1)/m]$. Then:
--
--   1. (10) The long-run inventory cost, as a function of the safety stock, has the unique minimizer $i^\star=\sigma_iz_i$ and the minimum value $C^\star_i=\sigma_i(h+b)\varphi[z_i]\ge0$.
--   2. (11) For every safety stock, the long-run local production cost, as a function of the capacity, has the unique minimizer $k^\star=\mu\gamma+\sigma_qz_q$ and the minimum value $C^\star_q=u\mu\gamma+um\sigma_q\varphi[z_q]\ge0$.
--   3. (12) The long-run purchasing cost is $C^\star_p=p(1-\gamma)\mu\ge0$.
--   4. (13) The total long-run average cost, as a function of $(i^\star,k)\in\mathbb R^2$, has the unique minimizer $(\sigma_iz_i,\ \mu\gamma+\sigma_qz_q)$ and the minimum value
--   $$C^{\mathrm{TBS\text{-}POUT},k^\star}=C^\star_i+C^\star_q+C^\star_p=\sigma_i(h+b)\varphi[z_i]+\sigma_qum\varphi[z_q]+((u-p)\gamma+p)\mu\ \ge 0 .$$
--
--   This identifies the optimized dual-sourcing cost with a closed form that is affine in $\gamma$.
--
--   **Formalization Note** The printed proposition leaves $\sigma_i,\sigma_q$ "to be determined" and remarks that correlated demand is allowed. Here the demand is iid and $\sigma_i,\sigma_q$ are the values (14). Safety stock and capacity range over $\mathbb R$ (the linearized model allows $k^\star<0$), $m>1$, and long-run averages are taken of expected period costs. "Optimal" is stated as an attained lower bound together with uniqueness of the minimizer.
-- source:
--   Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 9, Proposition 1, (10)–(13)

import Mathlib
import Definitions.Def_SpeedFactory_BreakEven_Model
import Definitions.Def_SpeedFactory_BreakEven_Dynamics

open MeasureTheory ProbabilityTheory

namespace SpeedFactory.BreakEven

/-- Proposition 1. Boute, Disney, Gijsbrechts, Van Mieghem, Dual Sourcing and Smoothing under Non-Stationary Demand Time Series: Re-shoring with SpeedFactories, accepted manuscript (revised Nov 28, 2020), p. 9, Proposition 1, (10)–(13).

Under iid `N(µ, σ)` demand, TBS-POUT with allocation `γ ∈ [0, 1]` and smoothing `α ∈ (−1, 1)`,
writing `σ_i, σ_q` for the (14) values:
* (10) the long-run inventory cost is minimized over the safety stock exactly at
  `i⋆ = σ_i z_i`, `z_i = Φ⁻¹[b/(b + h)]`, with minimum `C⋆_i = σ_i(h + b)φ[z_i] ≥ 0`;
* (11) for every safety stock, the long-run local production cost is minimized over the capacity
  exactly at `k⋆ = µγ + σ_q z_q`, `z_q = Φ⁻¹[(m − 1)/m]`, with minimum
  `C⋆_q = uµγ + umσ_qφ[z_q] ≥ 0`;
* (12) the long-run purchasing cost is `C⋆_p = p(1 − γ)µ ≥ 0`;
* (13) the total long-run cost is minimized over `(i⋆, k)` exactly at `(σ_i z_i, µγ + σ_q z_q)`
  with minimum `C^{TBS-POUT,k⋆} = σ_i(h + b)φ[z_i] + σ_q umφ[z_q] + ((u − p)γ + p)µ ≥ 0`.

**Formalization Note.** iid demand (the printed "identically" plus §5's "iid"), `m > 1`,
`α ∈ (−1, 1)`, `i⋆, k ∈ ℝ` with negative orders allowed (the linearized model), and the
expected Cesàro reading of (5). The printed Proposition 1 leaves `σ_i, σ_q` "to be determined";
here they are the iid values (14). Minimality is stated with `IsLeast` (attained lower bound)
plus uniqueness of the minimizer. -/
theorem proposition_1 (M : Model) (hM : M.Standing) {γ α : ℝ} (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Ioo (-1 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ → Ω → ℝ) (hd : IIDNormalDemand M P d) (i0 : ℝ) :
    let Ci := sigmaI M α * (M.h + M.b) * stdNormalPDF (zi M)
    let Cq := M.u * M.μ * γ + M.u * M.m * sigmaQ M α * stdNormalPDF (zq M)
    let Cp := M.p * (1 - γ) * M.μ
    let C13 := sigmaI M α * (M.h + M.b) * stdNormalPDF (zi M)
      + sigmaQ M α * M.u * M.m * stdNormalPDF (zq M) + ((M.u - M.p) * γ + M.p) * M.μ
    let iOpt := sigmaI M α * zi M
    let kOpt := M.μ * γ + sigmaQ M α * zq M
    -- (10)
    (IsLeast (Set.range fun s : ℝ => lrInvCostTBS M γ α s i0 P d) Ci ∧
      lrInvCostTBS M γ α iOpt i0 P d = Ci ∧
      ∀ s : ℝ, lrInvCostTBS M γ α s i0 P d = Ci → s = iOpt) ∧
    -- (11)
    (∀ s : ℝ, IsLeast (Set.range fun k : ℝ => lrCapCostTBS M γ α s k i0 P d) Cq ∧
      lrCapCostTBS M γ α s kOpt i0 P d = Cq ∧
      ∀ k : ℝ, lrCapCostTBS M γ α s k i0 P d = Cq → k = kOpt) ∧
    -- (12)
    lrAvg (fun _ => M.p * (M.μ * (1 - γ))) = Cp ∧
    -- (13)
    (IsLeast (Set.range fun x : ℝ × ℝ => lrCostTBS M γ α x.1 x.2 i0 P d) C13 ∧
      lrCostTBS M γ α iOpt kOpt i0 P d = C13 ∧
      ∀ x : ℝ × ℝ, lrCostTBS M γ α x.1 x.2 i0 P d = C13 → x = (iOpt, kOpt)) ∧
    C13 = Ci + Cq + Cp ∧
    0 ≤ Ci ∧ 0 ≤ Cq ∧ 0 ≤ Cp ∧ 0 ≤ C13 := by sorry

end SpeedFactory.BreakEven
