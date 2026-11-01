-- Prove2me | Theorems.Thm_VRAccelCLT_proposition_2
-- name    : VRAccelCLT.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:15.944273+00:00
-- url     : https://prove2.me/theorems/8a95efc2-9e02-4aa4-8c49-b1f3b2dcea17
-- title:
--   Proposition 2 (rate part; the complexity clause is not stated): geometric rate (22) and $\mathbb E\|x_k-x^*\|^2\le c\rho_2^k$ for Algorithm 2
-- statement:
--   Let $f$ satisfy Assumption 1 (i)–(ii) with constants $L,\eta>0$ and minimizer $x^*$, $f^*=f(x^*)$. Let $\alpha\in(0,1/L]$, $\gamma=\sqrt{\alpha\eta}$, $\beta=\frac{1-\gamma}{1+\gamma}$, $\rho_2\in(1-\gamma,1)$ and $N_k=\lceil\rho_2^{-(k+1)}\rceil$, let the gradient noise satisfy (5) with constant $\nu>0$, and let $(x_k,y_k)$ be a run of Algorithm 2 from $x_0=y_0$. Then:
--
--   1. for every $k\ge0$,
--   $$
--   \mathbb E[f(y_k)]-f^*\ \le\ \rho_2^{k}\Big(\frac{\eta+L}{2}\,\mathbb E\big[\|x_0-x^*\|^2\big]+\frac{\rho_2\nu^2}{\rho_2-(1-\gamma)}\Big(\alpha+\frac{(1-\gamma)\gamma}{2\eta}\Big)\Big);\tag{22}
--   $$
--   2. there is a constant $c>0$ (independent of $k$) with $\mathbb E\big[\|x_k-x^*\|^2\big]\le c\,\rho_2^{k}$ for every $k\ge0$.
--
--   With geometrically growing batches the accelerated method keeps a linear rate $\rho_2^k$ for any $\rho_2$ above the deterministic rate $1-\gamma$. The second bound is what makes the remainder of the CLT recursion negligible in Theorem 2.
--
--   **Formalization Note** Expectations of nonnegative quantities are lower Lebesgue integrals. The complexity sentence that follows (22) in the paper is not part of this statement: it fixes α = 1/L and ρ₂ = 1 − 1/(2√κ) only inside the proof (p.53), and its O(√κ ln(1/ε)) and O(√κ/ε) constants are left unquantified ("≈ … for large κ"), so it has no faithful formal reading; Theorem 2 does not use it. The milestone quotes exactly the two bounds stated here.
--
--   Differences from the source:
--   - generalization: noise w_{k,N_k} = sampled average (3) under Assumption 1(iii) → any F_{k+1}-measurable square-integrable noise w_k with (5) for a filtration F; reason: the paper derives (5) from (3) and Assumption 1(iii) (p.6) and uses nothing else about the noise; the sampled noise is an instance
--   - generalization: Algorithm 2 with positive β → β = (1−γ)/(1+γ) ≥ 0, allowed to be 0; reason: the theorem's own choice gives β = 0 when αη = 1 (η = L, α = 1/L); for β > 0 it is the source's statement
--   - encoding: x* the unique optimal solution, f* = f(x*) → x* any minimizer of f (∀ z, f x* ≤ f z), f* = f(x*); reason: strong convexity makes the minimizer unique; same instances
--   - encoding: E[‖x0 − x*‖²] → ‖x0 − x*‖² with x0 a fixed vector; reason: Algorithm 2 starts from arbitrary deterministic x0 = y0 ∈ ℝᵐ
--   - encoding: E[f(y_k) − f*] (and E[f(y_k)] − f*) → lower Lebesgue integral of the nonnegative f(y_k) − f(x*); reason: f(y_k) − f* ≥ 0 and is integrable under the hypotheses, so the values agree; no integrability side condition
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Proposition 2, eq. (22), p.12; proof in supplementary §H, p.53

import Mathlib
import Definitions.Def_VRAccelCLT_SmoothStronglyConvex
import Definitions.Def_VRAccelCLT_IsVRNoise
import Definitions.Def_VRAccelCLT_IsAlg2Run
import Definitions.Def_VRAccelCLT_batchSize

open MeasureTheory

namespace VRAccelCLT

/-- **Proposition 2: geometric rate for Algorithm 2.** Lei, Shanbhag, arXiv:2006.07769v3,
Proposition 2, p.12 (proof in the supplementary material, §H, p.53): "Let Assumption 1 hold.
Consider Algorithm 2, where α ∈ (0, 1/L], γ ≜ √αη, β ≜ (1−γ)/(1+γ), and Nk ≜ ⌈ρ2^{−(k+1)}⌉ with
ρ2 ∈ (1 − γ, 1). Then for any k ≥ 0, E[f(yk)] − f∗ ≤ ρ2^k (((η+L)/2) E[∥x0 − x∗∥2] +
(ρ2ν2/(ρ2 − (1−γ))) (α + (1−γ)γ/(2η))), (22) and E[∥xk − x∗∥2] ≤ cρ2^k for some constant c > 0."

Both bounds are stated: (22) for every `k ≥ 0`, and the existence of `c > 0` (depending on the data
but not on `k`) with `E‖x_k − x∗‖² ≤ cρ₂^k` for every `k`.

**Formalization Note.** Expectations are lower Lebesgue integrals of nonnegative functions;
`E[f(y_k)] − f∗` is written `E[f(y_k) − f∗]` (equal, `f(y_k)` being integrable). `x₀` is
deterministic. The complexity clause that follows (22) on p.12 is not part of this item. -/
theorem proposition_2 {m : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (L η ν α γ β ρ₂ : ℝ) (x0 xstar : EuclideanSpace ℝ (Fin m))
    (w x y : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (hA1 : SmoothStronglyConvex f L η) (hmin : ∀ z, f xstar ≤ f z)
    (hw : IsVRNoise μ ℱ w ν (batchSize ρ₂))
    (hα : 0 < α) (hαL : α ≤ 1 / L) (hγ : γ = Real.sqrt (α * η)) (hβ : β = (1 - γ) / (1 + γ))
    (hρ : 1 - γ < ρ₂) (hρ1 : ρ₂ < 1)
    (hrun : IsAlg2Run f α β x0 w x y) :
    (∀ k : ℕ,
      ∫⁻ ω, ENNReal.ofReal (f (y k ω) - f xstar) ∂μ ≤
        ENNReal.ofReal (ρ₂ ^ k * ((η + L) / 2 * ‖x0 - xstar‖ ^ 2 +
          ρ₂ * ν ^ 2 / (ρ₂ - (1 - γ)) * (α + (1 - γ) * γ / (2 * η))))) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ,
      ∫⁻ ω, ENNReal.ofReal (‖x k ω - xstar‖ ^ 2) ∂μ ≤ ENNReal.ofReal (c * ρ₂ ^ k) := by sorry

end VRAccelCLT
