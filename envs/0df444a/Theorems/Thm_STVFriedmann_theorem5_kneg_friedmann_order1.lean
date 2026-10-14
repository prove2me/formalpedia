-- Prove2me | Theorems.Thm_STVFriedmann_theorem5_kneg_friedmann_order1
-- name    : STVFriedmann.theorem5_kneg_friedmann_order1
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T01:59:23.797916+00:00
-- url     : https://prove2.me/theorems/c9d43369-a7d4-4df7-8704-018a474c22f0
-- title:
--   Theorem 5 (n = 1): the k < 0 Friedmann spacetime is the trajectory from SM to M
-- statement:
--   Fix $\Delta_0>0$. For $\theta>0$ put
--
--   $$
--   \frac{\bar t}{\Delta_0}=\frac12\bigl(\sinh 2\theta-2\theta\bigr),\qquad
--   \tilde z_2(\theta)=\frac{6(\sinh2\theta-2\theta)^2}{(\cosh2\theta-1)^3},\qquad
--   \tilde w_0(\theta)=\frac{(\sinh2\theta-2\theta)\sinh2\theta}{(\cosh2\theta-1)^2}.
--   $$
--
--   Then there is a solution $(z_2,w_0)(\bar t)$, $\bar t\in(0,\infty)$, of the order-1 STV ODE (2.34)–(2.35) such that
--
--   1. $(z_2,w_0)(\bar t)=(\tilde z_2(\theta),\tilde w_0(\theta))$ whenever $\bar t=\tfrac{\Delta_0}2(\sinh2\theta-2\theta)$, $\theta>0$;
--   2. $(z_2,w_0)(\bar t)\to SM=(\tfrac43,\tfrac23)$ as $\bar t\to0^+$;
--   3. $(z_2,w_0)(\bar t)\to M=(0,1)$ as $\bar t\to\infty$.
--
--   So the leading-order part of the $p=0$, $k=-1$ Friedmann spacetime with parameter $\Delta_0$ is the trajectory of the $2\times2$ phase portrait connecting $SM$ to $M$; $\Delta_0$ enters only as a log-time translation.
--
--   **Formalization Note** The STV ODE $\bar t\,\dot U=F(U)$ is written in log-time $\tau=\ln\bar t$ as $dU/d\tau=F(U)$ for all $\tau\in\mathbb R$; so $\bar t\to0^+$ is $\tau\to-\infty$ and $\bar t\to\infty$ is $\tau\to+\infty$.
-- source:
--   C. Alexander, B. Temple, Z. Vogler, The Instability of the Critical Friedmann Spacetime at the Big Bang as an Alternative to Dark Energy, arXiv:2510.14228v1 (2025), https://arxiv.org/abs/2510.14228, p. 14, Theorem 5 eqs. (2.40)-(2.42); p. 13, Section 2.5

import Mathlib
import Definitions.Def_STVFriedmann_basic

open Filter Topology Real

namespace STVFriedmann

/-- Theorem 5, (2.40)–(2.41): for every `Δ₀ > 0`, the leading-order `k = -1` Friedmann curve
`(z̃₂, w̃₀)(θ)`, with `t̄ = Δ₀ (sinh 2θ - 2θ)/2`, is a solution of the order-1 STV ODE taking
`SM` (as `t̄ → 0`) to `M` (as `t̄ → ∞`). -/
theorem theorem5_kneg_friedmann_order1 (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀) :
    ∃ U : ℝ → Fin 2 → ℝ, IsSTVSolution stvField1 U ∧
      (∀ θ : ℝ, 0 < θ → U (Real.log (Δ₀ * bigBangTime θ)) = friedmannCurve1 θ) ∧
      Tendsto U atBot (𝓝 restSM1) ∧ Tendsto U atTop (𝓝 restM1) := by sorry

end STVFriedmann
