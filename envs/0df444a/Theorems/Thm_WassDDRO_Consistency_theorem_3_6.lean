-- Prove2me | Theorems.Thm_WassDDRO_Consistency_theorem_3_6
-- name    : WassDDRO.Consistency.theorem_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:06:02.005006+00:00
-- url     : https://prove2.me/theorems/0d283eeb-c17c-4dc6-a962-acca4c61a30e
-- title:
--   Theorem 3.6, p. 8 — asymptotic consistency: P^∞-a.s. Ĵ_N → J⋆, and accumulation points of x̂_N are optimal for (1)
-- statement:
--   Let $E$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra, $m=\dim E\ne2$, and $P$ a probability distribution on $E$ supported on $\Xi\subseteq E$. Suppose Assumption 3.3 holds: for some $a>1$, $A=\mathbb E^P[\exp(\|\xi\|^a)]<\infty$; let $c_1,c_2>0$ be constants for which the concentration inequality (7) holds, and $\varepsilon_N(\beta)$ the radius (8). Let $\beta_N\in(0,1)$, $N\in\mathbb N$, satisfy
--   $$
--   \sum_{N=1}^\infty\beta_N<\infty\qquad\text{and}\qquad\lim_{N\to\infty}\varepsilon_N(\beta_N)=0 .
--   $$
--   Let $X\subseteq\mathbb R^n$, and $h:\mathbb R^n\times E\to\mathbb R$ with $h(x,\cdot)$ measurable for every $x$. Let $\hat\xi_1,\hat\xi_2,\ldots$ be i.i.d. with law $P$ (joint law $P^\infty$), and for each $N\ge1$ let $\widehat x_N\in X$ be an optimizer, and $\widehat J_N$ the optimal value, of the distributionally robust program (5) with ambiguity set $\mathbb B_{\varepsilon_N(\beta_N)}(\widehat P_N)$ built from the first $N$ samples. Let $J^\star=\inf_{x\in X}\mathbb E^P[h(x,\xi)]$ be the optimal value of (1).
--
--   1. If $h(x,\xi)$ is upper semicontinuous in $\xi\in\Xi$ for every $x\in X$, and there is $L\ge0$ with
--   $$
--   |h(x,\xi)|\le L(1+\|\xi\|)\qquad\text{for all }x\in X,\ \xi\in\Xi,
--   $$
--   then $P^\infty$-almost surely $\widehat J_N\ge J^\star$ for all sufficiently large $N$ and $\widehat J_N\to J^\star$ as $N\to\infty$.
--   2. If the assumptions of (1) hold, $X$ is closed, and $h(x,\xi)$ is lower semicontinuous in $x\in X$ for every $\xi\in\Xi$, then $P^\infty$-almost surely every accumulation point $x^\star$ of $(\widehat x_N)_{N\in\mathbb N}$ is an optimal solution of (1): $x^\star\in X$ and $\mathbb E^P[h(x^\star,\xi)]\le\mathbb E^P[h(x,\xi)]$ for all $x\in X$.
--
--   With radii shrinking at a rate dictated by the summable confidence levels $\beta_N$ (for example $\beta_N=\exp(-\sqrt N)$), the Wasserstein distributionally robust certificates and decisions are therefore consistent for the true stochastic program.
--
--   **Formalization Note** The paper writes "$\widehat J_N\downarrow J^\star$"; its proof establishes $J^\star\le\widehat J_N$ for all large $N$ and $\limsup\widehat J_N\le J^\star$, which is what is stated (convergence from above, not monotonicity). The constants $c_1,c_2$ are any constants satisfying (7), which Theorem 3.4 supplies under Assumption 3.3 for $m\ne2$; (7) and (8) are printed only for $m\ne2$. The loss is real-valued (the paper allows extended values, but the growth bound makes $h$ finite on $X\times\Xi$). The optimizers $\widehat x_N$ are required to exist only for samples in $\Xi$, which holds $P^\infty$-almost surely. The worst-case expectation counts distributions under which $h(x,\cdot)$ is integrable; under the growth bound every distribution in the ball integrates $h(x,\cdot)$, and Assumption 3.3 makes the Bochner integrals $\mathbb E^P[h(x,\xi)]$ genuine. "Accumulation point" is a cluster point of the sequence along $N\to\infty$; values of $\widehat x_0$ are irrelevant.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, Theorem 3.6, p. 8; proof pp. 9–10

import Mathlib
import Definitions.Def_WassDDRO_Consistency_Setting

open MeasureTheory Filter Topology

namespace WassDDRO.Consistency

/-- Theorem 3.6 (Asymptotic consistency), p. 8. Under Assumption 3.3, with constants `c₁, c₂`
for which (7) holds (`m ≠ 2`), `β_N ∈ (0, 1)` summable with `ε_N(β_N) → 0`, and `x̂_N` an
optimizer of (5) with ambiguity set `B_{ε_N(β_N)}(P̂_N)`:
(i) if `h(x, ·)` is upper semicontinuous on `Ξ` and `|h(x, ξ)| ≤ L(1 + ‖ξ‖)` on `X × Ξ`, then
`P^∞`-a.s. `Ĵ_N ≥ J⋆` eventually and `Ĵ_N → J⋆`;
(ii) if moreover `X` is closed and `h(·, ξ)` is lower semicontinuous on `X` for every `ξ ∈ Ξ`,
then `P^∞`-a.s. every accumulation point of `(x̂_N)` is an optimal solution of (1). -/
theorem theorem_3_6 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (Ξ : Set E) (hP : P Ξᶜ = 0)
    (a : ℝ) (ha : 1 < a) (hA : Integrable (fun ξ => Real.exp (‖ξ‖ ^ a)) P)
    (hm : Module.finrank ℝ E ≠ 2)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (h7 : Concentration7 P a c₁ c₂)
    (β : ℕ → ℝ) (hβ : ∀ N, 0 < β N ∧ β N < 1) (hsum : Summable β)
    (hlim : Tendsto (fun N => radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) atTop (𝓝 0))
    {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → E → ℝ)
    (hmeas : ∀ x, Measurable (h x))
    (xhat : (N : ℕ) → (Fin N → E) → EuclideanSpace ℝ (Fin n))
    (hopt : ∀ (N : ℕ) (ξhat : Fin N → E), 1 ≤ N → (∀ i, ξhat i ∈ Ξ) →
      xhat N ξhat ∈ X ∧ ∀ x ∈ X,
        WassersteinDRO.Duality.worstCaseRisk (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) 1 Ξ
            (WassersteinDRO.Duality.empiricalDistribution ξhat) (h (xhat N ξhat)) ≤
          WassersteinDRO.Duality.worstCaseRisk (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) 1 Ξ
            (WassersteinDRO.Duality.empiricalDistribution ξhat) (h x)) :
    ((∀ x ∈ X, UpperSemicontinuousOn (h x) Ξ) → ∀ L : ℝ, 0 ≤ L →
        (∀ x ∈ X, ∀ ξ ∈ Ξ, |h x ξ| ≤ L * (1 + ‖ξ‖)) →
        ∀ᵐ ω ∂(P_inf P),
          (∀ᶠ N in atTop, trueValue X h P ≤
            droValue X h (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) Ξ (fun i : Fin N => ω i)) ∧
          Tendsto (fun N => droValue X h (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) Ξ
            (fun i : Fin N => ω i)) atTop (𝓝 (trueValue X h P))) ∧
    ((∀ x ∈ X, UpperSemicontinuousOn (h x) Ξ) → ∀ L : ℝ, 0 ≤ L →
        (∀ x ∈ X, ∀ ξ ∈ Ξ, |h x ξ| ≤ L * (1 + ‖ξ‖)) →
        IsClosed X → (∀ ξ ∈ Ξ, LowerSemicontinuousOn (fun x => h x ξ) X) →
        ∀ᵐ ω ∂(P_inf P), ∀ xstar : EuclideanSpace ℝ (Fin n),
          MapClusterPt xstar atTop (fun N => xhat N (fun i : Fin N => ω i)) →
          xstar ∈ X ∧ ∀ x ∈ X, ∫ ξ, h xstar ξ ∂P ≤ ∫ ξ, h x ξ ∂P) := by sorry

end WassDDRO.Consistency
