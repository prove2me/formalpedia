-- Prove2me | Theorems.Thm_WassDDRO_Consistency_theorem_3_5
-- name    : WassDDRO.Consistency.theorem_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:05:10.551975+00:00
-- url     : https://prove2.me/theorems/07cc07d4-e722-4ab9-99bb-5123ac4202f0
-- title:
--   Theorem 3.5, p. 8 — finite sample guarantee: P^N{E^P[h(x̂_N, ξ)] > Ĵ_N} ≤ β for the radius ε_N(β)
-- statement:
--   Let $E$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra, $m=\dim E\ne2$, and let $P$ be a probability distribution on $E$ supported on $\Xi\subseteq E$ (that is, $P(E\setminus\Xi)=0$). Suppose Assumption 3.3 holds: for some $a>1$,
--   $$
--   A=\mathbb E^P\big[\exp(\|\xi\|^a)\big]<\infty,
--   $$
--   and let $c_1,c_2>0$ be constants for which the concentration inequality (7) holds. Fix $N\ge1$ and $\beta\in(0,1)$, a feasible set $X\subseteq\mathbb R^n$ and a loss $h:\mathbb R^n\times E\to\mathbb R$ with $h(x,\cdot)$ measurable for every $x$ and $P$-integrable for every $x\in X$. Let $\widehat x_N$ be an optimizer of the distributionally robust program (5) with ambiguity set $\mathbb B_{\varepsilon_N(\beta)}(\widehat P_N)$: for every sample $\widehat\Xi_N=\{\hat\xi_1,\dots,\hat\xi_N\}\subseteq\Xi$, $\widehat x_N\in X$ and $\widehat x_N$ minimizes $x\mapsto\sup_{Q\in\mathbb B_{\varepsilon_N(\beta)}(\widehat P_N)}\mathbb E^Q[h(x,\xi)]$ over $X$. Let $\widehat J_N$ be the optimal value of (5). Then the finite sample guarantee (2) holds:
--   $$
--   P^N\Big\{\widehat\Xi_N:\ \mathbb E^P\big[h(\widehat x_N,\xi)\big]>\widehat J_N\Big\}\le\beta,
--   \quad\text{equivalently}\quad
--   P^N\Big\{\widehat\Xi_N:\ \mathbb E^P\big[h(\widehat x_N,\xi)\big]\le\widehat J_N\Big\}\ge1-\beta .
--   $$
--
--   The certificate $\widehat J_N$ is thus an upper confidence bound, at level $1-\beta$, on the out-of-sample cost of the data-driven decision.
--
--   **Formalization Note** The probability is stated for the failure event, as an outer measure, because the success event need not be measurable ($\widehat x_N$ is an arbitrary selection of optimizers). The constants $c_1,c_2$ enter as any constants satisfying (7) (Theorem 3.4 supplies them); $m\ne2$ is the scope of (7) and (8). The optimizer is required only for samples in $\Xi$, as in §2 ($\widehat\Xi_N\subseteq\Xi$). The loss is real-valued and $P$-integrability of $h(x,\cdot)$ on $X$ is assumed, a specialization of the paper's extended-valued loss: the worst-case expectation counts only distributions under which $h(x,\cdot)$ is integrable, so without this hypothesis $P$ itself would not be counted.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, Theorem 3.5, p. 8; (2) p. 5, (5) p. 6, (7)–(8) p. 8

import Mathlib
import Definitions.Def_WassDDRO_Consistency_Setting

open MeasureTheory

namespace WassDDRO.Consistency

/-- Theorem 3.5 (Finite sample guarantee), p. 8. Under Assumption 3.3, with constants
`c₁, c₂` for which (7) holds (`m ≠ 2`), `β ∈ (0, 1)`, `N ≥ 1`, and `x̂_N` an optimizer of (5)
with ambiguity set `B_{ε_N(β)}(P̂_N)`, the guarantee (2) holds in failure-set form:
`P^N{E^P[h(x̂_N, ξ)] > Ĵ_N} ≤ β`. -/
theorem theorem_3_5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (Ξ : Set E) (hP : P Ξᶜ = 0)
    (a : ℝ) (ha : 1 < a) (hA : Integrable (fun ξ => Real.exp (‖ξ‖ ^ a)) P)
    (hm : Module.finrank ℝ E ≠ 2)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (h7 : Concentration7 P a c₁ c₂)
    (N : ℕ) (hN : 1 ≤ N) (b : ℝ) (hb : 0 < b ∧ b < 1)
    {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → E → ℝ)
    (hmeas : ∀ x, Measurable (h x)) (hint : ∀ x ∈ X, Integrable (h x) P)
    (xh : (Fin N → E) → EuclideanSpace ℝ (Fin n))
    (hopt : ∀ ξhat : Fin N → E, (∀ i, ξhat i ∈ Ξ) →
      xh ξhat ∈ X ∧ ∀ x ∈ X,
        WassersteinDRO.Duality.worstCaseRisk (radius c₁ c₂ a (Module.finrank ℝ E) N b) 1 Ξ
            (WassersteinDRO.Duality.empiricalDistribution ξhat) (h (xh ξhat)) ≤
          WassersteinDRO.Duality.worstCaseRisk (radius c₁ c₂ a (Module.finrank ℝ E) N b) 1 Ξ
            (WassersteinDRO.Duality.empiricalDistribution ξhat) (h x)) :
    (Measure.pi fun _ : Fin N => P)
        {ξhat | ¬ (((∫ ξ, h (xh ξhat) ξ ∂P : ℝ) : EReal) ≤
          droValue X h (radius c₁ c₂ a (Module.finrank ℝ E) N b) Ξ ξhat)} ≤
      ENNReal.ofReal b := by sorry

end WassDDRO.Consistency
