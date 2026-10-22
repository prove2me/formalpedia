-- Prove2me | Theorems.Thm_UnifErgHW_Diffusion_psi_properties
-- name    : UnifErgHW.Diffusion.psi_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:49.922002+00:00
-- url     : https://prove2.me/theorems/f43aa79e-7446-4064-93df-c4a17c71506b
-- title:
--   p. 7 — the cut-off ψ is convex and C², and ψ″_ε ≤ (3/2)ε²
-- statement:
--   Let $\psi:\mathbb R\to\mathbb R$ be the cut-off
--   $$
--   \psi(t)=\begin{cases}-\tfrac12, & t\le -1,\\ (t+1)^3-\tfrac12(t+1)^4-\tfrac12, & t\in[-1,0],\\ t, & t\ge 0,\end{cases}
--   $$
--   and for $\varepsilon>0$ let $\psi_\varepsilon(t)=\psi(\varepsilon t)$. Then $\psi$ is convex and of class $C^2$, it is constant $-\tfrac12$ for $t\le-1$ and equal to $t$ for $t\ge0$, $\psi_\varepsilon(t)=\varepsilon t$ for $t\ge 0$, and
--   $$
--   \psi_\varepsilon''(t)\le\tfrac32\,\varepsilon^2\qquad\text{for all }t\in\mathbb R .
--   $$
--
--   These facts are what make $V=\exp(\Psi^*_{\varepsilon,\theta})$ a $C^2$ function whose second-order term in the generator is of order $\varepsilon$.
--
--   **Formalization Note** $\psi$ is the published `cutoff`, written there as $-t^4/2-t^3+t$ on $(-1,0)$; the statement checks that this agrees with the printed formula on $[-1,0]$. $\psi''_\varepsilon$ is the second derivative `deriv (deriv (psiEps ε))`.
-- source:
--   Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 7, §2.4 (definition of ψ and ψ_ε)

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

/-- Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 7 (§2.4): the cut-off `ψ` is a convex `C²` function, constant `−1/2` on `(−∞, −1]`,
the identity on `[0, ∞)`, equal to `(t + 1)³ − ½(t + 1)⁴ − ½` on `[−1, 0]`; its scaling
`ψ_ε(t) = ψ(εt)` satisfies `ψ_ε(t) = εt` for `t ≥ 0` and `ψ″_ε ≤ (3/2)ε²` for every `ε > 0`.

Formalization Note. `ψ` is the published `GPhNGIDiffusion.EMError.cutoff`, written there as
`−t⁴/2 − t³ + t` on `(−1, 0)`; the polynomial clause ties it to the printed formula. `ψ″_ε` is
`deriv (deriv (psiEps ε))`. -/
theorem psi_properties :
    ContDiff ℝ 2 cutoff ∧ ConvexOn ℝ Set.univ cutoff ∧
      (∀ t : ℝ, t ≤ -1 → cutoff t = -1 / 2) ∧
      (∀ t : ℝ, 0 ≤ t → cutoff t = t) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 0, cutoff t = (t + 1) ^ 3 - 1 / 2 * (t + 1) ^ 4 - 1 / 2) ∧
      (∀ ε : ℝ, 0 < ε → ∀ t : ℝ, 0 ≤ t → psiEps ε t = ε * t) ∧
      ∀ ε : ℝ, 0 < ε → ∀ t : ℝ, deriv (deriv (psiEps ε)) t ≤ 3 / 2 * ε ^ 2 := by sorry

end UnifErgHW.Diffusion
