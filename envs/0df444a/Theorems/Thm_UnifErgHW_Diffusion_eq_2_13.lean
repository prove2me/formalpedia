-- Prove2me | Theorems.Thm_UnifErgHW_Diffusion_eq_2_13
-- name    : UnifErgHW.Diffusion.eq_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:09.410227+00:00
-- url     : https://prove2.me/theorems/8f7a18cd-456b-43d8-a5ed-d40bd15610e1
-- title:
--   (2.13a)–(2.13b), p. 8 — the identities for ⟨∇Ψ_ε(x), b(x,u)⟩ and ⟨∇Ψ(−x), b(x,u)⟩
-- statement:
--   Assume the centred drift $b(x,u)=-\frac{\varrho}{m}Me-M(x-\langle e,x\rangle^+u)-\langle e,x\rangle^+\Gamma u$ and put $\beta_i=\gamma_i/\mu_i$. For every $\varepsilon>0$, $x\in\mathbb R^m$ and control value $u$,
--   $$
--   \big\langle\nabla\Psi_\varepsilon(x),b(x,u)\big\rangle=-\frac{\varrho}{m}\sum_i\psi_\varepsilon'(x_i)-\sum_i\psi_\varepsilon'(x_i)x_i+\langle e,x\rangle^+\sum_i\psi_\varepsilon'(x_i)(1-\beta_i)^+u_i-\langle e,x\rangle^+\sum_i\psi_\varepsilon'(x_i)(\beta_i-1)^+u_i ,
--   $$
--   $$
--   \big\langle\nabla\Psi(-x),b(x,u)\big\rangle=\frac{\varrho}{m}\sum_i\psi'(-x_i)+\sum_i\psi'(-x_i)x_i-\langle e,x\rangle^+\sum_i\psi'(-x_i)(1-\beta_i)^+u_i+\langle e,x\rangle^+\sum_i\psi'(-x_i)(\beta_i-1)^+u_i .
--   $$
--
--   These identities are the starting point of the drift inequalities of Lemma 2.1.
--
--   **Formalization Note** $\nabla\Psi(-x)$ denotes the gradient at $x$ of the function $y\mapsto\Psi(-y)$. The identities hold for every vector $u$, in particular for $u\in\Delta$.
-- source:
--   Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 8, (2.13a)–(2.13b)

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

/-- Arapostathis, Hmedi, Pang, On uniform exponential ergodicity of Markovian multiclass many-server queues in the Halfin–Whitt regime, arXiv:1812.03528v3, p. 8, (2.13a)–(2.13b): with `βᵢ = γᵢ/µᵢ` and the centred drift (2.6),
`⟨∇Ψ_ε(x), b(x,u)⟩ = −(ϱ/m)∑ᵢψ′_ε(xᵢ) − ∑ᵢψ′_ε(xᵢ)xᵢ + ⟨e,x⟩⁺∑ᵢψ′_ε(xᵢ)(1 − βᵢ)⁺uᵢ − ⟨e,x⟩⁺∑ᵢψ′_ε(xᵢ)(βᵢ − 1)⁺uᵢ`
and
`⟨∇Ψ(−x), b(x,u)⟩ = (ϱ/m)∑ᵢψ′(−xᵢ) + ∑ᵢψ′(−xᵢ)xᵢ − ⟨e,x⟩⁺∑ᵢψ′(−xᵢ)(1 − βᵢ)⁺uᵢ + ⟨e,x⟩⁺∑ᵢψ′(−xᵢ)(βᵢ − 1)⁺uᵢ`.

Formalization Note. `∇Ψ(−x)` is the gradient of `y ↦ Ψ(−y)` at `x`; `b(x, u)` is `ctrlDrift D u x`
with `ℓ = −(ϱ/m)Me` (`IsCentered`). The identities hold for every vector `u`, in particular every
`u ∈ ∆`. -/
theorem eq_2_13 {m : ℕ} (hm : 0 < m) (D : ManyServerQED.Scheduling.DiffusionData m) (ϱ : ℝ)
    (hℓ : IsCentered D ϱ) (ε : ℝ) (hε : 0 < ε) (x : EthierKurtz.SDEState m) (u : Fin m → ℝ) :
    ⟪gradient (PsiEps D ε) x, ctrlDrift D u x⟫ =
        -(ϱ / m) * ∑ i, deriv (psiEps ε) (x i) - ∑ i, deriv (psiEps ε) (x i) * x i
          + max (∑ i, x i) 0 *
              ∑ i, deriv (psiEps ε) (x i) * max (1 - D.theta i / D.mu i) 0 * u i
          - max (∑ i, x i) 0 *
              ∑ i, deriv (psiEps ε) (x i) * max (D.theta i / D.mu i - 1) 0 * u i ∧
    ⟪gradient (fun y => Psi D (-y)) x, ctrlDrift D u x⟫ =
        ϱ / m * ∑ i, deriv cutoff (-(x i)) + ∑ i, deriv cutoff (-(x i)) * x i
          - max (∑ i, x i) 0 *
              ∑ i, deriv cutoff (-(x i)) * max (1 - D.theta i / D.mu i) 0 * u i
          + max (∑ i, x i) 0 *
              ∑ i, deriv cutoff (-(x i)) * max (D.theta i / D.mu i - 1) 0 * u i := by sorry

end UnifErgHW.Diffusion
