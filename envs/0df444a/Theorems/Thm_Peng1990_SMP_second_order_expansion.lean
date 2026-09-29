-- Prove2me | Theorems.Thm_Peng1990_SMP_second_order_expansion
-- name    : Peng1990.SMP.second_order_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:32:22.92599+00:00
-- url     : https://prove2.me/theorems/c303e45d-dbdb-4a29-84b2-29f6b60170c7
-- title:
--   Lemma 1 — the spike-perturbed state equals $y+y_1+y_2$ up to $o(\varepsilon^2)$ in mean square
-- statement:
--   Assume (3). Let $u$ be an admissible control with trajectory $y$, let $0\le\tau<T$, and let $v$ be an $\mathcal F^\tau$-measurable random variable with values in $U$ and $\sup_{\omega\in\Omega}|v(\omega)|<\infty$. For $0<\varepsilon\le T-\tau$ let $u^\varepsilon$ be the spike variation of $u$ on $[\tau,\tau+\varepsilon]$ by $v$, $y^\varepsilon$ the trajectory of (1) for $u^\varepsilon$, and $y_1^\varepsilon$, $y_2^\varepsilon$ solutions of the variational equations (5), (6). Then
--   $$\sup_{0\le t\le T}E\big|y^\varepsilon(t)-y(t)-y_1^\varepsilon(t)-y_2^\varepsilon(t)\big|^2=o(\varepsilon^2)\qquad(\varepsilon\to0^+),$$
--   that is, for every $\delta>0$ there is $\varepsilon_0>0$ with $E|y^\varepsilon(t)-y(t)-y_1(t)-y_2(t)|^2\le\delta\varepsilon^2$ for all $0<\varepsilon<\varepsilon_0$ and all $t\in[0,T]$.
--
--   The paper prints (4) as $\varepsilon^{-2}\sup_t E|\cdots|^2\le C$. Its proof establishes the $o(\varepsilon^2)$ bound (via (10)), and Lemma 2 needs it: the $O(\varepsilon^2)$ bound alone only gives an $O(\varepsilon)$ error in the cost, not $o(\varepsilon)$. The $o(\varepsilon^2)$ form is stated here.
--
--   This second-order expansion of the state is the first step of the maximum principle: it replaces the perturbed state by the solutions of two linear equations.
--
--   **Formalization Note** In Section 3 the pair $(y,u)$ is optimal, but the proof of Lemma 1 does not use optimality; the statement is made for every admissible pair. "$\varepsilon$ sufficiently small" is the filter $\varepsilon\to0^+$. Solutions of (1), (5), (6) are quantified universally (strong solutions are unique).
-- source:
--   Peng, A General Stochastic Maximum Principle for Optimal Control Problems, SIAM J. Control Optim. 28(4), 1990, https://doi.org/10.1137/0328054, p. 968, Lemma 1, (4)–(6), with the spike variation defined above it; the $o(\varepsilon^2)$ strength is from the proof, p. 970, (10)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_Peng1990_SMP_ControlProblem
import Definitions.Def_Peng1990_SMP_Adjoint

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped ENNReal NNReal Matrix

namespace Peng1990.SMP

theorem second_order_expansion {Ω : Type*} [MeasurableSpace Ω] {n k d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (cp : ControlProblem n k d) (h3 : Assumption3 cp)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
    (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (hu : IsAdmissible cp (brownianFiltration hB) P u)
    (hy : SolvesState cp (brownianFiltration hB) P B u y)
    (τ : ℝ≥0) (hτ : τ < cp.T) (v : Ω → Fin k → ℝ)
    (hv : Measurable[brownianFiltration hB τ] v) (hvU : ∀ ω, v ω ∈ cp.U)
    (hvb : ∃ M : ℝ, ∀ ω, ‖v ω‖ ≤ M)
    (yε y₁ y₂ : ℝ → ℝ≥0 → Ω → Fin n → ℝ)
    (hyε : ∀ ε ∈ Set.Ioc (0 : ℝ) ((cp.T : ℝ) - τ),
      SolvesState cp (brownianFiltration hB) P B (spike u τ ε v) (yε ε))
    (hy₁ : ∀ ε ∈ Set.Ioc (0 : ℝ) ((cp.T : ℝ) - τ),
      SolvesFirstVariation cp (brownianFiltration hB) P B y u (spike u τ ε v) (y₁ ε))
    (hy₂ : ∀ ε ∈ Set.Ioc (0 : ℝ) ((cp.T : ℝ) - τ),
      SolvesSecondVariation cp (brownianFiltration hB) P B y u (spike u τ ε v) (y₁ ε) (y₂ ε)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ≤ cp.T,
      ∫⁻ ω, ‖yε ε t ω - y t ω - y₁ ε t ω - y₂ ε t ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (δ * ε ^ 2) := by sorry

end Peng1990.SMP
