-- Prove2me | Theorems.Thm_VRAccelCLT_lemma_2
-- name    : VRAccelCLT.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:10.487991+00:00
-- url     : https://prove2.me/theorems/049475f4-19d3-49dc-b790-6a52734bee4b
-- title:
--   Lemma 2: $\mathbb E[f(y_k)-f^*]$ bound (11) for Algorithm 2
-- statement:
--   Let $f$ satisfy Assumption 1 (i)–(ii) with constants $L,\eta>0$ and minimizer $x^*$, $f^*=f(x^*)$. Let $(N_k)_{k\ge0}$ be any sequence of positive integers and let the gradient noise $w_k$ satisfy (5) with constant $\nu>0$. Let $\alpha\in(0,1/L]$, $\gamma=\sqrt{\alpha\eta}$ and $\beta=\frac{1-\gamma}{1+\gamma}$, and let $(x_k,y_k)$ be a run of Algorithm 2 from $x_0=y_0$. Then for every $k\ge1$,
--
--   $$
--   \mathbb E[f(y_k)-f^*]\ \le\ \frac{(\eta+L)(1-\gamma)^k}{2}\,\mathbb E\big[\|x_0-x^*\|^2\big]+\nu^2\Big(\alpha+\frac{(1-\gamma)\gamma}{2\eta}\Big)\sum_{i=0}^{k-1}\frac{(1-\gamma)^i}{N_{k-1-i}} .\tag{11}
--   $$
--
--   The first term is the deterministic accelerated rate $(1-\sqrt{\alpha\eta})^k$; the second accumulates the sampling variance, discounted geometrically. Proposition 2 specializes it to geometric batch sizes.
--
--   **Formalization Note** The expectation of the nonnegative gap is a lower Lebesgue integral. $x_0$ is deterministic, so $\mathbb E\|x_0-x^*\|^2=\|x_0-x^*\|^2$.
--
--   Differences from the source:
--   - generalization: noise w_{k,N_k} = sampled average (3) under Assumption 1(iii) → any F_{k+1}-measurable square-integrable noise w_k with (5) for a filtration F; reason: the paper derives (5) from (3) and Assumption 1(iii) (p.6) and uses nothing else about the noise; the sampled noise is an instance
--   - generalization: Algorithm 2 with positive β → β = (1−γ)/(1+γ) ≥ 0, allowed to be 0; reason: the theorem's own choice gives β = 0 when αη = 1 (η = L, α = 1/L); for β > 0 it is the source's statement
--   - encoding: x* the unique optimal solution, f* = f(x*) → x* any minimizer of f (∀ z, f x* ≤ f z), f* = f(x*); reason: strong convexity makes the minimizer unique; same instances
--   - encoding: E[‖x0 − x*‖²] → ‖x0 − x*‖² with x0 a fixed vector; reason: Algorithm 2 starts from arbitrary deterministic x0 = y0 ∈ ℝᵐ
--   - encoding: E[f(y_k) − f*] (and E[f(y_k)] − f*) → lower Lebesgue integral of the nonnegative f(y_k) − f(x*); reason: f(y_k) − f* ≥ 0 and is integrable under the hypotheses, so the values agree; no integrability side condition
--   - encoding: a positive integer sequence {N_k} → N : ℕ → ℕ with N k > 0 for all k; reason: same objects
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Lemma 2, eq. (11), p.8; proof in supplementary §F, pp.48–51

import Mathlib
import Definitions.Def_VRAccelCLT_SmoothStronglyConvex
import Definitions.Def_VRAccelCLT_IsVRNoise
import Definitions.Def_VRAccelCLT_IsAlg2Run

open MeasureTheory

namespace VRAccelCLT

/-- **Lemma 2: sub-optimality bound for Algorithm 2.** Lei, Shanbhag, arXiv:2006.07769v3, Lemma 2,
p.8 (proof in the supplementary material, §F, pp.48–51): "Let Algorithm 2 be applied to the problem
(1). Suppose Assumption 1 holds and α ∈ (0, 1/L]. Set β = (1−γ)/(1+γ) with γ = √αη. Then for any
k ≥ 1, E[f(yk) − f∗] ≤ ((η+L)(1−γ)^k/2) E[∥x0 − x∗∥2] + ν2 (α + (1−γ)γ/(2η))
Σ_{i=0}^{k−1} (1−γ)^i/N_{k−1−i}. (11)"

For any positive batch sizes `N_k`, gradient noise `w` with (5), and a run `(x, y)` of Algorithm 2
from `x₀ = y₀`, the bound (11) holds for every `k ≥ 1`.

**Formalization Note.** `E[f(y_k) − f∗]` is the lower Lebesgue integral of the nonnegative
`f(y_k) − f(x∗)` (no integrability side condition); `x₀` is deterministic, so
`E‖x₀ − x∗‖² = ‖x₀ − x∗‖²`. Assumption 1 (iii) is used through its consequence (5)
(`IsVRNoise`). -/
theorem lemma_2 {m : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (L η ν α γ β : ℝ) (x0 xstar : EuclideanSpace ℝ (Fin m)) (N : ℕ → ℕ) (hN : ∀ k, 0 < N k)
    (w x y : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (hA1 : SmoothStronglyConvex f L η) (hmin : ∀ z, f xstar ≤ f z)
    (hw : IsVRNoise μ ℱ w ν N)
    (hα : 0 < α) (hαL : α ≤ 1 / L) (hγ : γ = Real.sqrt (α * η)) (hβ : β = (1 - γ) / (1 + γ))
    (hrun : IsAlg2Run f α β x0 w x y) :
    ∀ k : ℕ, 1 ≤ k →
      ∫⁻ ω, ENNReal.ofReal (f (y k ω) - f xstar) ∂μ ≤
        ENNReal.ofReal ((η + L) * (1 - γ) ^ k / 2 * ‖x0 - xstar‖ ^ 2 +
          ν ^ 2 * (α + (1 - γ) * γ / (2 * η)) *
            ∑ i ∈ Finset.range k, (1 - γ) ^ i / (N (k - 1 - i) : ℝ)) := by sorry

end VRAccelCLT
