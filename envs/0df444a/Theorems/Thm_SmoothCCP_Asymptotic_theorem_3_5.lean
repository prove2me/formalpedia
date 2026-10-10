-- Prove2me | Theorems.Thm_SmoothCCP_Asymptotic_theorem_3_5
-- name    : SmoothCCP.Asymptotic.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:50.222663+00:00
-- url     : https://prove2.me/theorems/66544c51-05dc-440f-be11-ec5978446d2d
-- title:
--   Theorem 3.5, p. 10 — v^N_ε → v* and D(S^N_ε, S) → 0 w.p.1 as N → ∞ and ε → 0
-- statement:
--   Consider the chance-constrained program (1.1), $\min_{x\in X} f(x)$ subject to $\mathbb P(C(x,\xi)\le 0)\ge 1-\alpha$, with optimal solution set $S$ and optimal value $v^*$, and its smoothed sample approximation (2.4), $\min_{x\in X} f(x)$ subject to $F^N_\varepsilon(0;x) \ge 1-\alpha$, with solution set $S^N_\varepsilon$ and value $v^N_\varepsilon$, built from the first $N$ draws of an i.i.d. sequence $\xi_1,\xi_2,\dots$ with law $\mathbb P_\xi$.
--
--   Assume:
--   1. $0<\alpha<1$, $X \subseteq\mathbb R^n$ is compact and $f$ is continuous;
--   2. (Assumption 3.1) for each $x\in X$, $C(x,\xi)$ has a continuous distribution;
--   3. (Assumption 3.2) $C(x,\cdot)$ is measurable for every $x \in X$ and $C(\cdot,\xi)$ is continuous for almost every $\xi$;
--   4. (Assumption 3.3) there is an optimal solution $\bar x$ of (1.1) such that for every $\eta>0$ some $x\in X$ has $\|x-\bar x\|\le\eta$ and $F(0;x)>1-\alpha$;
--   5. $\gamma_\varepsilon$ is admissible for every $\varepsilon>0$.
--
--   Then, with probability one, as $N\to\infty$ and $\varepsilon\to0$:
--   $$S^N_\varepsilon \neq \emptyset \text{ eventually},\qquad v^N_\varepsilon \to v^*,\qquad \mathbb D(S^N_\varepsilon, S) = \sup_{x\in S^N_\varepsilon}\operatorname{dist}(x,S) \to 0.$$
--
--   The theorem says that the smoothed sample-based approximation is consistent in both the sample size and the smoothing parameter jointly.
--
--   **Formalization Note** The limit is the product filter $N\to\infty$ times $\varepsilon\to0^+$ on $\mathbb N\times\mathbb R$, and one null set serves all three conclusions. The feasible set of (2.4) is written as $F^N_\varepsilon(0;x)\ge1-\alpha$, the form the paper's proof uses, because the quantile $Q^{1-\alpha}_\varepsilon$ of (2.4) exists only when $(1-\alpha)N\notin\mathbb Z$; where it exists, the two feasible sets coincide. The eventual nonemptiness of $S^N_\varepsilon$ is part of the conclusion, so the optimal values are genuine minima. The deviation is stated as "for every $\eta>0$, eventually every point of $S^N_\varepsilon$ lies within distance $\eta$ of $S$", with $S$ nonempty by Assumption 3.3. Compactness implies closedness of $X$. Decisions carry the sup norm, which does not change Assumption 3.3. The smoothing family $\gamma_\varepsilon$ is arbitrary across $\varepsilon$.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, Theorem 3.5, p. 10

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
import Definitions.Def_SmoothCCP_Asymptotic_Optimization

open MeasureTheory Filter Topology

namespace SmoothCCP.Asymptotic

/-- Theorem 3.5, p. 10: if X is compact, f is continuous and Assumptions 3.1–3.3 hold, then
w.p.1, as N → ∞ and ε → 0⁺: S^N_ε is eventually nonempty, v^N_ε → v*, and
D(S^N_ε, S) = sup_{x ∈ S^N_ε} dist(x, S) → 0. -/
theorem theorem_3_5
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
    ∀ᵐ ω ∂P,
      (∀ᶠ p in atTop ×ˢ 𝓝[>] (0 : ℝ),
        (optSet f (saaFeasible C X p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) α)).Nonempty) ∧
      Tendsto (fun p : ℕ × ℝ =>
          optVal f (saaFeasible C X p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) α))
        (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (optVal f (SmoothCCP.Feasibility.trueFeasible Pξ C X α))) ∧
      (∀ η > 0, ∀ᶠ p in atTop ×ˢ 𝓝[>] (0 : ℝ),
        ∀ x ∈ optSet f (saaFeasible C X p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) α),
          Metric.infDist x (optSet f (SmoothCCP.Feasibility.trueFeasible Pξ C X α)) < η) := by sorry

end SmoothCCP.Asymptotic
