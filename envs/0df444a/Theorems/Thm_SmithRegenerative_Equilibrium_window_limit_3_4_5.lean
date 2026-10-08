-- Prove2me | Theorems.Thm_SmithRegenerative_Equilibrium_window_limit_3_4_5
-- name    : SmithRegenerative.Equilibrium.window_limit_3_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:35:37.754881+00:00
-- url     : https://prove2.me/theorems/76d0900a-f13f-4cd6-a150-4e94a0c8e58a
-- title:
--   (3·4·5) — window limit for φ_A(v){1 − F(v)} of locally bounded variation, ϖ = 0, μ₁ < ∞
-- statement:
--   Let $E$ be an aperiodic equilibrium process with cycle law $F$ of finite mean $\mu_1$. Fix a boundary condition $z$, a state set $A$ in its class $\mathcal A$, and let $H_{K_z}$ be the renewal measure of its delay law. Suppose $g(v)=\varphi_A(v)\{1-F(v)\}$ is of bounded variation on every finite time interval. Then for $\Delta > 0$,
--   $$
--   \lim_{t\to\infty} \int_{t-\Delta}^{t} g(t-v)\, dH_{K_z}(v) = \frac{1}{\mu_1} \int_0^\Delta g(v)\, dv.
--   $$
--
--   This is the case (iv)$''_a$ in the proof of Theorem 2. Together with (3·4·7) it gives the corresponding case of the limit theorem.
--
--   **Formalization Note** Only values of $\varphi_A$ on $[0,\Delta]$ enter. The integral over $[t-\Delta, t]$ is closed at both ends.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, §3·4, proof of Theorem 2, (3·4·5), p. 16

import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_EquilibriumProcess

namespace SmithRegenerative.Equilibrium

open MeasureTheory Filter Topology

/-- **The window limit (3·4·5)** (Smith 1955, §3·4, proof of Theorem 2, p. 16; unnumbered result).
For an aperiodic equilibrium process `E` with `μ₁ < ∞`, a boundary condition `z` and a set
`A ∈ 𝒜`, let `g(v) = φ_A(v){1 − F(v)}` be of bounded variation on every finite time interval.
Then, for `Δ > 0`,
`lim_{t→∞} ∫_{t−Δ}^t g(t − v) dH_{K_z}(v) = (1/μ₁) ∫₀^Δ g(v) dv`.

Formalization Note: `φ_A` is measurable by the equilibrium-process definition; only its values on
`[0, Δ]` enter.
The Stieltjes integral `∫_{t−Δ}^t` is over the closed interval `[t − Δ, t]`. -/
theorem window_limit_3_4_5 {Ω 𝔛 Z : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝔛]
    (E : EquilibriumProcess Ω 𝔛 Z) (z : Z) (A : Set 𝔛) (hA : A ∈ E.𝒜)
    (hper : IsAperiodic E.F) (hμ : mean E.F < ⊤) (Δ : ℝ) (hΔ : 0 < Δ)
    (hbv : ∀ b : ℝ, BoundedVariationOn
      (fun v => E.φ A v * (E.F (Set.Ioi v)).toReal) (Set.Icc 0 b)) :
    Tendsto (fun t : ℝ => ∫ v in Set.Icc (t - Δ) t,
        E.φ A (t - v) * (E.F (Set.Ioi (t - v))).toReal
          ∂(renewalMeasure (E.K z) E.F)) atTop
      (𝓝 ((mean E.F).toReal⁻¹ * ∫ v in Set.Ioc 0 Δ,
        E.φ A v * (E.F (Set.Ioi v)).toReal)) := by sorry

end SmithRegenerative.Equilibrium
