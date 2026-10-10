-- Prove2me | Theorems.Thm_SmoothCCP_Asymptotic_eq_3_3
-- name    : SmoothCCP.Asymptotic.eq_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:37.22433+00:00
-- url     : https://prove2.me/theorems/38baaef8-62c5-4f03-a7d0-939b3033d29a
-- title:
--   (3.3), p. 11 — lim inf v^N_ε ≥ v* w.p.1: eventually f(x) ≥ v* − η on the feasible set of (2.4)
-- statement:
--   Assume the hypotheses of Theorem 3.5: $0<\alpha<1$, $X$ compact, $f$ continuous, an i.i.d. sample, Assumptions 3.1–3.3 (with optimal solution $\bar x$ of (1.1)), and an admissible $\gamma_\varepsilon$ for every $\varepsilon > 0$. Let $v^* = \min_{x\in X_\alpha} f(x)$ be the optimal value of (1.1).
--
--   Then, with probability one, for every $\eta > 0$ there are $N_0$ and $\varepsilon_0>0$ such that for all $N \ge N_0$ and $0<\varepsilon\le\varepsilon_0$,
--   $$f(x) \ge v^* - \eta \quad \text{for every } x \in X \text{ with } F^N_\varepsilon(0;x) \ge 1-\alpha.$$
--   In particular $\liminf v^N_\varepsilon \ge v^*$ with probability one as $N\to\infty$ and $\varepsilon\to0$, which is (3.3).
--
--   This is the lower half of the convergence $v^N_\varepsilon \to v^*$ in Theorem 3.5.
--
--   **Formalization Note** The paper states (3.3) along sequences $(N_k,\varepsilon_k) \to (\infty,0)$ for the optimal values $v^{N_k}_{\varepsilon_k}$. The statement here bounds $f$ on the whole feasible set of (2.4), which implies the liminf of the optimal values wherever they exist and does not read an infimum over a possibly empty set. The joint limit is the product filter $N\to\infty$, $\varepsilon\to0^+$; the null set does not depend on $\eta$. Assumption 3.3 is needed so that $X_\alpha$ is nonempty and $v^*$ is attained.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, proof of Theorem 3.5, (3.3), p. 11

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
import Definitions.Def_SmoothCCP_Asymptotic_Optimization

open MeasureTheory Filter Topology

namespace SmoothCCP.Asymptotic

/-- (3.3), p. 11, robust form of lim inf v^N_ε ≥ v* w.p.1: for every η > 0, for all N large and
ε > 0 small, every feasible point x of (2.4) has f(x) ≥ v* − η. -/
theorem eq_3_3
    {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξmeas : ∀ i, Measurable (ξ i))
    (hξind : ProbabilityTheory.iIndepFun ξ P) (hξlaw : ∀ i, P.map (ξ i) = Pξ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (X : Set (Fin n → ℝ)) (hX : IsCompact X)
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (C : (Fin n → ℝ) → Ξ → ℝ)
    (hA31 : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (hA32meas : ∀ x ∈ X, Measurable (C x))
    (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s))
    (xbar : Fin n → ℝ) (hxbar : xbar ∈ optSet f (SmoothCCP.Feasibility.trueFeasible Pξ C X α))
    (hA33 : ∀ η > 0, ∃ x ∈ X, ‖x - xbar‖ ≤ η ∧ 1 - α < SmoothCCP.Feasibility.cdf Pξ C 0 x)
    (γ : ℝ → ℝ → ℝ) (hγ : ∀ ε > 0, SmoothCCP.Feasibility.AdmissibleGamma ε (γ ε)) :
    ∀ᵐ ω ∂P, ∀ η > 0, ∀ᶠ p in atTop ×ˢ 𝓝[>] (0 : ℝ),
      ∀ x ∈ saaFeasible C X p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) α,
        optVal f (SmoothCCP.Feasibility.trueFeasible Pξ C X α) - η ≤ f x := by sorry

end SmoothCCP.Asymptotic
