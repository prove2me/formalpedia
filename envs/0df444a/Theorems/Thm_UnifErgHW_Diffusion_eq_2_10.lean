-- Prove2me | Theorems.Thm_UnifErgHW_Diffusion_eq_2_10
-- name    : UnifErgHW.Diffusion.eq_2_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:13.9178+00:00
-- url     : https://prove2.me/theorems/ff0dff9b-5b6d-463b-9620-945da90a2c1b
-- title:
--   (2.10), p. 7 — Ψ*_{ε,θ} follows ‖·‖_1 (lower constant corrected to m(1∨εθ)/(2µ_min))
-- statement:
--   Let $\varepsilon,\theta>0$ and let $0<\mu_{\mathrm{lo}}\le\mu_i\le\mu_{\mathrm{hi}}$ for all classes $i$ (for instance $\mu_{\mathrm{lo}}=\mu_{\min}$, $\mu_{\mathrm{hi}}=\mu_{\max}$). Then for every $x\in\mathbb R^m$
--   $$
--   \varepsilon\frac{1\wedge\theta}{\mu_{\mathrm{hi}}}\|x\|_1-\frac{m\,(1\vee\varepsilon\theta)}{2\mu_{\mathrm{lo}}}\;\le\;\Psi^*_{\varepsilon,\theta}(x)\;\le\;\varepsilon\frac{1\vee\theta}{\mu_{\mathrm{lo}}}\|x\|_1 .
--   $$
--
--   Thus $\Psi^*_{\varepsilon,\theta}$ grows like the $\ell^1$ norm, so $V=\exp(\Psi^*_{\varepsilon,\theta})$ is coercive; this gives the compact sets and the tightness used in the proof of Theorem 2.1(b).
--
--   **Formalization Note** The paper prints the additive constant $-\frac m2$, which is false when $\mu_{\min}<1$: for $m=1$, $\mu=0.1$, $\theta\le1$ and $x\le-1/\varepsilon$ one has $\Psi^*=\varepsilon\theta|x|/\mu-5$. Since $\psi\ge-\frac12$, each coordinate loses at most $(1\vee\varepsilon\theta)/(2\mu_i)$, which gives the stated constant. The upper bound is as printed.
-- source:
--   Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 7, (2.10)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov

open MeasureTheory
open scoped NNReal ENNReal RealInnerProductSpace
open GPhNGIDiffusion.EMError (SolvesAdditiveSDE IsTransitionFunction IsInvariantMeasure generator tvNormWeighted cutoff partial2)

namespace UnifErgHW.Diffusion

/-- Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 7, (2.10), with the additive constant of the lower bound corrected: for `ε, θ > 0`,
`ε(1 ∧ θ)/µ_max ‖x‖₁ − m(1 ∨ εθ)/(2µ_min) ≤ Ψ*_{ε,θ}(x) ≤ ε(1 ∨ θ)/µ_min ‖x‖₁`.

Formalization Note. The page prints `− m/2` in the lower bound, which fails when `µ_min < 1`
(`m = 1`, `µ = 0.1`, `θ ≤ 1`, `x ≤ −1/ε`: `Ψ* = εθ|x|/µ − 5`). Since `ψ ≥ −1/2`, each coordinate
loses at most `(1 ∨ εθ)/(2µᵢ)`, which gives the posed constant. `µ_min`, `µ_max` are replaced by any
bounds `0 < µlo ≤ µᵢ ≤ µhi`; the sharpest instance is `µlo = µ_min`, `µhi = µ_max`. -/
theorem eq_2_10 {m : ℕ} (D : ManyServerQED.Scheduling.DiffusionData m) (ε θ : ℝ)
    (hε : 0 < ε) (hθ : 0 < θ) (μlo μhi : ℝ) (hlo : 0 < μlo)
    (hμ : ∀ i, μlo ≤ D.mu i ∧ D.mu i ≤ μhi) (x : EthierKurtz.SDEState m) :
    ε * min 1 θ / μhi * l1 x - m * max 1 (ε * θ) / (2 * μlo) ≤ PsiStar D ε θ x ∧
      PsiStar D ε θ x ≤ ε * max 1 θ / μlo * l1 x := by sorry

end UnifErgHW.Diffusion
