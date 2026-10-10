-- Prove2me | Theorems.Thm_SmoothCCP_Asymptotic_eq_3_4
-- name    : SmoothCCP.Asymptotic.eq_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:47:05.005189+00:00
-- url     : https://prove2.me/theorems/2c3fbeca-620f-43ab-a17a-feb02c0457f7
-- title:
--   (3.4), p. 11 — lim sup v^N_ε ≤ v* w.p.1: eventually (2.4) has a feasible x with f(x) ≤ v* + η
-- statement:
--   Let $0<\alpha<1$, $X \subseteq\mathbb R^n$ closed, $f$ continuous, $\xi_1,\xi_2,\dots$ i.i.d. with law $\mathbb P_\xi$, Assumptions 3.1–3.3 (with optimal solution $\bar x$ of (1.1)), and an admissible $\gamma_\varepsilon$ for every $\varepsilon>0$. Let $v^* = f(\bar x)$ be the optimal value of (1.1).
--
--   Then, with probability one, for every $\eta > 0$ there are $N_0$ and $\varepsilon_0>0$ such that for all $N\ge N_0$ and $0<\varepsilon\le\varepsilon_0$ there is
--   $$x \in X \text{ with } F^N_\varepsilon(0;x) \ge 1-\alpha \text{ and } f(x) \le v^* + \eta.$$
--   In particular $\limsup v^N_\varepsilon \le v^*$ with probability one as $N\to\infty$ and $\varepsilon\to0$, which is (3.4).
--
--   This is the upper half of the convergence $v^N_\varepsilon \to v^*$ in Theorem 3.5.
--
--   **Formalization Note** The statement asserts a feasible point of (2.4) with value at most $v^*+\eta$, which implies the limsup of the optimal values and also shows that the feasible set of (2.4) is eventually nonempty. Compactness of $X$ is not needed for this half and is not assumed; $X$ is closed, the standing assumption of the paper. The joint limit is the product filter $N\to\infty$, $\varepsilon\to0^+$; the null set does not depend on $\eta$.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, proof of Theorem 3.5, (3.4), p. 11

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
import Definitions.Def_SmoothCCP_Asymptotic_Optimization

open MeasureTheory Filter Topology

namespace SmoothCCP.Asymptotic

/-- (3.4), p. 11, robust form of lim sup v^N_ε ≤ v* w.p.1: for every η > 0, for all N large and
ε > 0 small, (2.4) has a feasible point x with f(x) ≤ v* + η. X need not be compact. -/
theorem eq_3_4
    {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξmeas : ∀ i, Measurable (ξ i))
    (hξind : ProbabilityTheory.iIndepFun ξ P) (hξlaw : ∀ i, P.map (ξ i) = Pξ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (X : Set (Fin n → ℝ)) (hX : IsClosed X)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (C : (Fin n → ℝ) → Ξ → ℝ)
    (hA31 : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (hA32meas : ∀ x ∈ X, Measurable (C x))
    (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s))
    (xbar : Fin n → ℝ) (hxbar : xbar ∈ optSet f (SmoothCCP.Feasibility.trueFeasible Pξ C X α))
    (hA33 : ∀ η > 0, ∃ x ∈ X, ‖x - xbar‖ ≤ η ∧ 1 - α < SmoothCCP.Feasibility.cdf Pξ C 0 x)
    (γ : ℝ → ℝ → ℝ) (hγ : ∀ ε > 0, SmoothCCP.Feasibility.AdmissibleGamma ε (γ ε)) :
    ∀ᵐ ω ∂P, ∀ η > 0, ∀ᶠ p in atTop ×ˢ 𝓝[>] (0 : ℝ),
      ∃ x ∈ saaFeasible C X p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) α,
        f x ≤ optVal f (SmoothCCP.Feasibility.trueFeasible Pξ C X α) + η := by sorry

end SmoothCCP.Asymptotic
