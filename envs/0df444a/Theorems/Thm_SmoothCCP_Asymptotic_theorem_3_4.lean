-- Prove2me | Theorems.Thm_SmoothCCP_Asymptotic_theorem_3_4
-- name    : SmoothCCP.Asymptotic.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:45:39.207008+00:00
-- url     : https://prove2.me/theorems/c2cd53f9-3d0b-492a-8d3f-d6e034f8ce96
-- title:
--   Theorem 3.4, p. 10 — w.p.1, sup_{x∈U} |F^N_ε(0;x) − F(0;x)| → 0 as N → ∞ and ε → 0
-- statement:
--   Let $X \subseteq \mathbb R^n$ be closed, let $\xi_1,\xi_2,\dots$ be i.i.d. with law $\mathbb P_\xi$, and let $C$ satisfy Assumption 3.1 (for each $x\in X$, $C(x,\xi)$ has a continuous distribution) and Assumption 3.2 ($C$ is Carathéodory: $C(x,\cdot)$ measurable for every $x\in X$, $C(\cdot,\xi)$ continuous for almost every $\xi$). For every $\varepsilon > 0$ let $\gamma_\varepsilon$ be admissible. Then for every compact $U \subseteq X$, with probability one,
--   $$\sup_{x\in U}\bigl|F^N_\varepsilon(0;x) - F(0;x)\bigr| \to 0 \quad \text{as } N\to\infty \text{ and } \varepsilon\to 0,$$
--   where $F^N_\varepsilon$ uses the first $N$ draws.
--
--   The limit is joint: for every $\eta > 0$ there are $N_\eta$ and $\varepsilon_\eta > 0$ such that the supremum is below $\eta$ for all $N \ge N_\eta$ and all $0 < \varepsilon \le \varepsilon_\eta$. This uniform convergence of the smoothed empirical constraint function is what drives the consistency of optimal values and solutions in Theorem 3.5.
--
--   **Formalization Note** The joint limit is the product filter $N \to \infty$ times $\varepsilon \to 0^+$ on $\mathbb N \times \mathbb R$, not an iterated limit; the null set is fixed before the filter is applied. Decisions carry the sup norm.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, Theorem 3.4, p. 10

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting

open MeasureTheory Filter Topology

namespace SmoothCCP.Asymptotic

/-- Theorem 3.4, p. 10: under Assumptions 3.1 and 3.2, w.p.1,
sup_{x ∈ U} |F^N_ε(0; x) − F(0; x)| → 0 as N → ∞ and ε → 0, for every compact U ⊆ X. -/
theorem theorem_3_4
    {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → Ξ) (hξmeas : ∀ i, Measurable (ξ i))
    (hξind : ProbabilityTheory.iIndepFun ξ P) (hξlaw : ∀ i, P.map (ξ i) = Pξ)
    (X : Set (Fin n → ℝ)) (hX : IsClosed X) (C : (Fin n → ℝ) → Ξ → ℝ)
    (hA31 : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (hA32meas : ∀ x ∈ X, Measurable (C x))
    (hA32cont : ∀ᵐ s ∂Pξ, Continuous (fun x => C x s))
    (γ : ℝ → ℝ → ℝ) (hγ : ∀ ε > 0, SmoothCCP.Feasibility.AdmissibleGamma ε (γ ε))
    (U : Set (Fin n → ℝ)) (hU : IsCompact U) (hUX : U ⊆ X) :
    ∀ᵐ ω ∂P,
      TendstoUniformlyOn
        (fun (p : ℕ × ℝ) (x : Fin n → ℝ) =>
          SmoothCCP.Feasibility.sampleCdf C p.2 (γ p.2) (fun i : Fin p.1 => ξ i ω) 0 x)
        (fun x => SmoothCCP.Feasibility.cdf Pξ C 0 x) (atTop ×ˢ 𝓝[>] (0 : ℝ)) U := by sorry

end SmoothCCP.Asymptotic
