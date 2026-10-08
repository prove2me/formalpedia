-- Prove2me | Theorems.Thm_WassDDRO_Consistency_lemma_3_7
-- name    : WassDDRO.Consistency.lemma_3_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:05:50.526993+00:00
-- url     : https://prove2.me/theorems/ea7e1fbc-2314-4f4e-b29d-fccba8bb76c1
-- title:
--   Lemma 3.7, p. 9 — any data-dependent Q̂_N ∈ B_{ε_N(β_N)}(P̂_N) converges to P in d_W, P^∞-almost surely
-- statement:
--   Let $E$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra, $m=\dim E\ne2$, and $P$ a probability distribution on $E$ supported on $\Xi$. Suppose Assumption 3.3 holds with exponent $a>1$, and let $c_1,c_2>0$ be constants for which the concentration inequality (7) holds. Let $\beta_N\in(0,1)$, $N\in\mathbb N$, satisfy
--   $$
--   \sum_{N=1}^\infty\beta_N<\infty\qquad\text{and}\qquad\lim_{N\to\infty}\varepsilon_N(\beta_N)=0,
--   $$
--   with $\varepsilon_N(\beta)$ the radius (8). Let $\widehat Q_N$, $N\ge1$, be any distributions, possibly depending on the training data, with $\widehat Q_N\in\mathbb B_{\varepsilon_N(\beta_N)}(\widehat P_N)$, where $\widehat P_N$ is the empirical distribution of the first $N$ samples of the i.i.d. sequence $\hat\xi_1,\hat\xi_2,\ldots\sim P$. Then
--   $$
--   P^\infty\Big\{\lim_{N\to\infty}d_W\big(P,\widehat Q_N\big)=0\Big\}=1 .
--   $$
--
--   Every distribution in the shrinking Wasserstein balls thus converges to the true distribution; this is the step in the proof of Theorem 3.6 that turns worst-case expectations into true expectations in the limit.
--
--   **Formalization Note** The selection $\widehat Q_N(\omega)$ is any function of the whole sample sequence $\omega$ that lies in the ball whenever the samples lie in $\Xi$ (as they do $P^\infty$-almost surely); in the paper it may depend on the training data. "Almost surely" is stated as a $P^\infty$-almost-everywhere statement. $c_1,c_2$ are any constants satisfying (7), which Theorem 3.4 provides for $m\ne2$. The paper's parenthetical "and thus weakly" is a remark citing the literature and is not part of the statement.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, Lemma 3.7, p. 9

import Mathlib
import Definitions.Def_WassDDRO_Consistency_Setting

open MeasureTheory Filter Topology

namespace WassDDRO.Consistency

/-- Lemma 3.7 (Convergence of distributions), p. 9. Under Assumption 3.3, with constants
`c₁, c₂` for which (7) holds (`m ≠ 2`), and `β_N ∈ (0, 1)` summable with `ε_N(β_N) → 0`,
any (data-dependent) selection `Q̂_N ∈ B_{ε_N(β_N)}(P̂_N)` satisfies
`P^∞{lim_N d_W(P, Q̂_N) = 0} = 1`. -/
theorem lemma_3_7 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (Ξ : Set E) (hP : P Ξᶜ = 0)
    (a : ℝ) (ha : 1 < a) (hA : Integrable (fun ξ => Real.exp (‖ξ‖ ^ a)) P)
    (hm : Module.finrank ℝ E ≠ 2)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (h7 : Concentration7 P a c₁ c₂)
    (β : ℕ → ℝ) (hβ : ∀ N, 0 < β N ∧ β N < 1) (hsum : Summable β)
    (hlim : Tendsto (fun N => radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) atTop (𝓝 0))
    (Qhat : ℕ → (ℕ → E) → Measure E)
    (hQ : ∀ N (ω : ℕ → E), 1 ≤ N → (∀ i, ω i ∈ Ξ) →
      Qhat N ω ∈ WassersteinDRO.Duality.ambiguitySet
        (radius c₁ c₂ a (Module.finrank ℝ E) N (β N)) 1 Ξ
        (WassersteinDRO.Duality.empiricalDistribution (fun i : Fin N => ω i))) :
    ∀ᵐ ω ∂(P_inf P),
      Tendsto (fun N => WassersteinDRO.Duality.wassersteinDistance 1 P (Qhat N ω)) atTop (𝓝 0) := by sorry

end WassDDRO.Consistency
