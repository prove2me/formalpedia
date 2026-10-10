-- Prove2me | Theorems.Thm_SmoothCCP_Asymptotic_optSet_eventually_nonempty
-- name    : SmoothCCP.Asymptotic.optSet_eventually_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:40.311326+00:00
-- url     : https://prove2.me/theorems/9809db38-5502-4452-bcf6-2ca0db317b07
-- title:
--   Proof of Theorem 3.5, pp. 10–11 — w.p.1, S^N_ε ≠ ∅ for all N large and ε > 0 small
-- statement:
--   Assume the hypotheses of Theorem 3.5: $0 < \alpha < 1$; $X \subseteq \mathbb R^n$ compact; $f : \mathbb R^n \to \mathbb R$ continuous; $\xi_1,\xi_2,\dots$ i.i.d. with law $\mathbb P_\xi$; Assumption 3.1 (for each $x\in X$, $C(x,\xi)$ has a continuous distribution); Assumption 3.2 ($C(x,\cdot)$ measurable for $x\in X$, $C(\cdot,\xi)$ continuous for almost every $\xi$); Assumption 3.3 (there is an optimal solution $\bar x$ of (1.1) such that for every $\eta > 0$ some $x \in X$ has $\|x-\bar x\| \le \eta$ and $F(0;x) > 1-\alpha$); and an admissible $\gamma_\varepsilon$ for every $\varepsilon > 0$.
--
--   Then, with probability one, there are $N_0$ and $\varepsilon_0 > 0$ such that for all $N \ge N_0$ and $0 < \varepsilon \le \varepsilon_0$ the approximation (2.4)
--   $$\min_{x \in X} f(x) \quad \text{s.t.}\quad F^N_\varepsilon(0;x) \ge 1-\alpha$$
--   has an optimal solution: $S^N_\varepsilon \neq \emptyset$.
--
--   This guarantees that $v^N_\varepsilon$ and $S^N_\varepsilon$ in Theorem 3.5 are genuine minima for all large $N$ and small $\varepsilon$.
--
--   **Formalization Note** $N_0$ and $\varepsilon_0$ depend on the sample path; the paper fixes them before writing "w.p.1", but the true statement is "almost surely, eventually". The feasible set of (2.4) is written as $F^N_\varepsilon(0;x)\ge 1-\alpha$, the form the proof uses, rather than through $Q^{1-\alpha}_\varepsilon$, which exists only when $(1-\alpha)N\notin\mathbb Z$. Compactness implies closedness of $X$, so closedness is not a separate hypothesis. The norm in Assumption 3.3 is the sup norm; since the condition is for every $\eta > 0$, any norm on $\mathbb R^n$ gives the same assumption.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, proof of Theorem 3.5, pp. 10–11, second paragraph

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
import Definitions.Def_SmoothCCP_Asymptotic_Optimization

open MeasureTheory Filter Topology

namespace SmoothCCP.Asymptotic

/-- Proof of Theorem 3.5, pp. 10–11: w.p.1, the solution set S^N_ε of (2.4) is nonempty for all
N large enough and ε > 0 small enough. -/
theorem optSet_eventually_nonempty
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
    ∀ᵐ ω ∂P, ∀ᶠ p in atTop ×ˢ 𝓝[>] (0 : ℝ),
      (optSet f (saaFeasible C X p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) α)).Nonempty := by sorry

end SmoothCCP.Asymptotic
