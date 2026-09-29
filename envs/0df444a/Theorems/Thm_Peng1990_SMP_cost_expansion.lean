-- Prove2me | Theorems.Thm_Peng1990_SMP_cost_expansion
-- name    : Peng1990.SMP.cost_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:33:04.19315+00:00
-- url     : https://prove2.me/theorems/474da5d1-5cf8-4400-8e4d-4d9a5f86274c
-- title:
--   Lemma 2 — second-order expansion of the cost is $\ge o(\varepsilon)$ at an optimal control
-- statement:
--   Assume (3) and let $(y,u)$ be an optimal pair. Let $\tau$, $v$, $u^\varepsilon$ be as in Lemma 1, and let $y_1=y_1^\varepsilon$, $y_2=y_2^\varepsilon$ solve (5), (6) for $0<\varepsilon\le T-\tau$. Then
--   $$\begin{aligned}&E\int_0^T\Big[l_x(y(s),u(s))\big(y_1(s)+y_2(s)\big)+\tfrac12 l_{xx}(y(s),u(s))y_1(s)y_1(s)\Big]ds+E\int_0^T\big(l(y(s),u^\varepsilon(s))-l(y(s),u(s))\big)ds\\&\quad+E\big(h_x(y(T))(y_1(T)+y_2(T))\big)+\tfrac12Eh_{xx}(y(T))y_1(T)y_1(T)\ \ge\ o(\varepsilon),\end{aligned}$$
--   meaning that there is a function $r$ with $r(\varepsilon)/\varepsilon\to0$ as $\varepsilon\to0^+$ such that the left side is at least $r(\varepsilon)$ for all sufficiently small $\varepsilon>0$.
--
--   This is inequality (11): the variation of the cost, expanded to second order in the state, is asymptotically nonnegative.
--
--   **Formalization Note** "$\ge o(\varepsilon)$" is read as above (limits $\varepsilon\to0^+$ with $\tau$, $v$ fixed). The expectations are Bochner integrals; each integrand is integrable under (3), the moment bounds on $u$ and $y$, and the boundedness of $v$.
-- source:
--   Peng, A General Stochastic Maximum Principle for Optimal Control Problems, SIAM J. Control Optim. 28(4), 1990, https://doi.org/10.1137/0328054, p. 970, Lemma 2, (11)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_Peng1990_SMP_ControlProblem
import Definitions.Def_Peng1990_SMP_Adjoint

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped ENNReal NNReal Matrix

namespace Peng1990.SMP

theorem cost_expansion {Ω : Type*} [MeasurableSpace Ω] {n k d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (cp : ControlProblem n k d) (h3 : Assumption3 cp)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
    (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (hopt : IsOptimalPair cp (brownianFiltration hB) P B y u)
    (τ : ℝ≥0) (hτ : τ < cp.T) (v : Ω → Fin k → ℝ)
    (hv : Measurable[brownianFiltration hB τ] v) (hvU : ∀ ω, v ω ∈ cp.U)
    (hvb : ∃ M : ℝ, ∀ ω, ‖v ω‖ ≤ M)
    (y₁ y₂ : ℝ → ℝ≥0 → Ω → Fin n → ℝ)
    (hy₁ : ∀ ε ∈ Set.Ioc (0 : ℝ) ((cp.T : ℝ) - τ),
      SolvesFirstVariation cp (brownianFiltration hB) P B y u (spike u τ ε v) (y₁ ε))
    (hy₂ : ∀ ε ∈ Set.Ioc (0 : ℝ) ((cp.T : ℝ) - τ),
      SolvesSecondVariation cp (brownianFiltration hB) P B y u (spike u τ ε v) (y₁ ε) (y₂ ε)) :
    ∃ r : ℝ → ℝ, r =o[𝓝[>] (0 : ℝ)] (fun ε => ε) ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      r ε ≤
        (∫ ω, ∫ s in Set.Icc (0 : ℝ) cp.T,
            (lX cp (y s.toNNReal ω) (u s.toNNReal ω) ⬝ᵥ (y₁ ε s.toNNReal ω + y₂ ε s.toNNReal ω)
              + (1 / 2 : ℝ) * d2 (fun x => cp.l x (u s.toNNReal ω)) (y s.toNNReal ω)
                  (y₁ ε s.toNNReal ω)) ∂volume ∂P)
        + (∫ ω, ∫ s in Set.Icc (0 : ℝ) cp.T,
            (cp.l (y s.toNNReal ω) (spike u τ ε v s.toNNReal ω)
              - cp.l (y s.toNNReal ω) (u s.toNNReal ω)) ∂volume ∂P)
        + (∫ ω, grad cp.h (y cp.T ω) ⬝ᵥ (y₁ ε cp.T ω + y₂ ε cp.T ω) ∂P)
        + (1 / 2 : ℝ) * ∫ ω, d2 cp.h (y cp.T ω) (y₁ ε cp.T ω) ∂P := by sorry

end Peng1990.SMP
