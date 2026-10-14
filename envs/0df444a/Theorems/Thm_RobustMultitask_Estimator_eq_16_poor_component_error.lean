-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_eq_16_poor_component_error
-- name    : RobustMultitask.Estimator.eq_16_poor_component_error
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:33:47.309557+00:00
-- url     : https://prove2.me/theorems/5c88a8c0-55b8-4730-b3e6-629b7f801150
-- title:
--   (16), p. 42 — P[‖(β̂†_RM − β†)_{ℐ_poor}‖₁ ≥ C₀d(3ζ+4η) maxᵢ √(σᵢ²/(nᵢψ) log(3/η))] ≤ 3d exp(−Nη²/9)
-- statement:
--   Work in the fixed-design multitask model with $N\ge 1$ tasks and dimension $d\ge 1$, under Assumption 1 with constant $\psi>0$. Let $\widehat\beta^\dagger_{\mathrm{RM}}$ be the shared estimate of Step 1 of Algorithm 1, computed with trimming level $\omega=\zeta+\eta$, and let $\mathcal I_{\mathrm{poor}}=\mathcal I^\zeta_{\mathrm{poor}}$ (Definition 2). Then for every constant $C_0>2$, every $0<\zeta<1/2$ and every $0<\eta\le 1/2-1/C_0-\zeta$,
--   $$\mathbb P\Big[\big\|(\widehat\beta^\dagger_{\mathrm{RM}}-\beta^\dagger)_{\mathcal I_{\mathrm{poor}}}\big\|_1\ \ge\ C_0d(3\zeta+4\eta)\max_{\iota\in[N]}\sqrt{\frac{\sigma_\iota^2}{n_\iota\psi}\log\frac{3}{\eta}}\ \Big]\ \le\ 3d\exp\Big(-\frac{N\eta^2}{9}\Big).$$
--
--   The shared estimate is accurate on the poorly-aligned components, where few tasks deviate from $\beta^\dagger$; this is the first of the two error terms of Proposition 5.
--
--   **Formalization Note** The constant $C_0$ is universally quantified and the trimming level is $\omega=\zeta+\eta$. The hypotheses $N\ge1$ and $d\ge1$ are explicit: for $d=0$ both sides of the inequality inside the event are $0$, the event is certain, and the bound $0$ would be false. The probability is the outer measure of the event.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 42, eq. (16)

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_Model
import Definitions.Def_RobustMultitask_Estimator_Algorithm
import Definitions.Def_RobustMultitask_Estimator_Alignment

namespace RobustMultitask.Estimator

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Equation (16), p. 42. In the fixed-design multitask model under Assumption 1, with
`N, d ≥ 1`, for every `C₀ > 2`, `0 < ζ < 1/2`, `0 < η ≤ 1/2 − 1/C₀ − ζ`, the shared estimate
`β̂†_RM` of Step 1 with trimming level `ω = ζ + η` satisfies
`P[‖(β̂†_RM − β†)_{ℐ_poor}‖₁ ≥ C₀ d (3ζ + 4η) max_{ι∈[N]} √(σ_ι²/(n_ιψ) log(3/η))] ≤ 3d exp(−Nη²/9)`,
where `ℐ_poor = ℐ^ζ_poor`. -/
theorem eq_16_poor_component_error {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    {N d : ℕ} (n : Fin N → ℕ) (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
    (ε : (j : Fin N) → Fin (n j) → Ω → ℝ)
    (hmodel : IsMultitaskModel P n X β βdag s σ ε) (hN : 0 < N) (hd : 0 < d)
    (ψ : ℝ) (hA1 : Assumption1 n X ψ)
    (C₀ ζ η : ℝ) (hC₀ : 2 < C₀) (hζ0 : 0 < ζ) (hζ1 : ζ < 1 / 2)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 2 - 1 / C₀ - ζ) :
    P {ω | C₀ * d * (3 * ζ + 4 * η)
            * (⨆ ι, Real.sqrt ((σ ι : ℝ) ^ 2 / ((n ι : ℝ) * ψ) * Real.log (3 / η)))
          ≤ l1 (restrict (poorlyAligned β βdag ζ)
              (sharedEst n X (ζ + η) (fun k => response X β ε k ω) - βdag))}
      ≤ ENNReal.ofReal (3 * d * Real.exp (-((N : ℝ) * η ^ 2) / 9)) := by sorry

end RobustMultitask.Estimator
