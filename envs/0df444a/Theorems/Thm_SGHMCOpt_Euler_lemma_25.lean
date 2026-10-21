-- Prove2me | Theorems.Thm_SGHMCOpt_Euler_lemma_25
-- name    : SGHMCOpt.Euler.lemma_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:12.401731+00:00
-- url     : https://prove2.me/theorems/08182730-412d-4044-8bda-5714f8d0bbd1
-- title:
--   Lemma 25, p. 69 — quadratic bounds: ‖∇f(x,z)‖ ≤ M‖x‖ + B and (m/3)‖x‖² − (b/2)log 3 ≤ f(x,z) ≤ (M/2)‖x‖² + B‖x‖ + A₀
-- statement:
--   Let $f:\mathbb R^d\times\mathcal Z\to\mathbb R$ satisfy parts (i), (ii) and (iii) of Assumption 1: each $f(\cdot,\zeta)$ is $C^1$ and non-negative with $|f(0,\zeta)|\le A_0$ and $\|\nabla f(0,\zeta)\|\le B$, its gradient is $M$-Lipschitz, and it is $(m,b)$-dissipative, $\langle x,\nabla f(x,\zeta)\rangle\ge m\|x\|^2-b$. Then for all $x\in\mathbb R^d$ and $\zeta\in\mathcal Z$,
--   $$\|\nabla f(x,\zeta)\|\le M\|x\|+B,\qquad \frac m3\|x\|^2-\frac b2\log3\ \le\ f(x,\zeta)\ \le\ \frac M2\|x\|^2+B\|x\|+A_0.$$
--
--   The loss therefore grows quadratically, with explicit constants; this is what makes the Gibbs law integrable and gives the drift constant $A$ of (2.2).
--
--   **Formalization Note** The paper states the lemma under parts (i) and (ii) only. The lower bound involves $m$ and $b$, which only part (iii) constrains, and is false without it ($f\equiv0$, $m=1$, $b=0$); the cited source (Raginsky–Rakhlin–Telgarsky 2017, Lemma 2) assumes dissipativity. Part (iii) is therefore a hypothesis here. `LossAssumption` also carries joint measurability of $f$, which the lemma does not use.
-- source:
--   arXiv:1809.04618v4, Lemma 25, p. 69 (citing Raginsky, Rakhlin, Telgarsky 2017, Lemma 2)

import Mathlib
import Definitions.Def_SGHMCOpt_Euler_Constants
import Definitions.Def_SGHMCOpt_Euler_Model

namespace SGHMCOpt.Euler

/-- Lemma 25, p. 69 (RRT17, Lemma 2), with part (iii) of Assumption 1 added to the printed
hypotheses "(i) and (ii)": for all `x ∈ ℝ^d` and `ζ`, `‖∇f(x, ζ)‖ ≤ M‖x‖ + B` and
`(m/3)‖x‖² − (b/2) log 3 ≤ f(x, ζ) ≤ (M/2)‖x‖² + B‖x‖ + A₀`. -/
theorem lemma_25 {d : ℕ} {𝒵 : Type*} [MeasurableSpace 𝒵] (f : E d → 𝒵 → ℝ) (p : Params)
    (hloss : LossAssumption f p) (x : E d) (ζ : 𝒵) :
    ‖gradient (fun y => f y ζ) x‖ ≤ p.M * ‖x‖ + p.B ∧
      p.m / 3 * ‖x‖ ^ 2 - p.b / 2 * Real.log 3 ≤ f x ζ ∧
      f x ζ ≤ p.M / 2 * ‖x‖ ^ 2 + p.B * ‖x‖ + p.A0 := by sorry

end SGHMCOpt.Euler
