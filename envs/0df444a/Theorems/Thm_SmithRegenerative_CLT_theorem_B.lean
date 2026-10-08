-- Prove2me | Theorems.Thm_SmithRegenerative_CLT_theorem_B
-- name    : SmithRegenerative.CLT.theorem_B
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:19.769925+00:00
-- url     : https://prove2.me/theorems/c9be2344-bc6c-4c85-9917-bef5b71691fd
-- title:
--   Theorem B (Anscombe 1952) — the central limit theorem for sums with a random number m_t of terms, m_t/ψ(t) → 1 in probability
-- statement:
--   Let $\psi$ be an unbounded, non-decreasing real function of a real variable $t$. For each $t$ let $m_t$ be a random variable with values in the positive integers, such that $m_t/\psi(t) \to 1$ in probability as $t \to \infty$. Let $y_1, y_2, \dots$ be independent, identically distributed real random variables on the same probability space with
--   $$E y_i = 0, \qquad \operatorname{var} y_i = \sigma^2, \qquad \sigma > 0.$$
--   Then for every real $\alpha$, as $t \to \infty$,
--   $$P\left\{ \frac{\sum_{i=1}^{m_t} y_i}{\sigma\,[\psi(t)]^{1/2}} \le \alpha \right\} \to \Phi(\alpha) = \int_{-\infty}^{\alpha} \frac{e^{-\theta^2/2}}{\sqrt{2\pi}}\,\mathrm{d}\theta.$$
--
--   No independence between the random index $m_t$ and the summands is assumed; this is what makes the theorem applicable to $m_t = n_t + 1$, the number of renewal cycles begun by time $t$, which is determined by the cycles themselves. It is the main tool of Smith's central limit theorems.
--
--   **Formalization Note** $\sigma > 0$ is implicit in the paper, which divides by $\sigma$. $\Phi$ is the distribution function of the standard normal law. The sequence starts at $y_1$.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, pp. 28–29, Theorem B (5·4·1)–(5·4·2), after Anscombe (1952)

import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.CLT

/-- Smith (1955), Theorem B, pp. 28–29 (Anscombe 1952, in Smith's form): "Let `ψ(t)` be an
unbounded, non-decreasing function of a real variable `t`. Let `m_t` be a proper random variable
taking positive integer values, and such that `m_t/ψ(t) → 1`, in probability. Let `{y_i}` be a
sequence of identically distributed, independent random variables, such that `Ey_i = 0`,
`var y_i = σ²` (5·4·1). Then, as `t → ∞`, `P{Σ₁^{m_t} y_i/(σ[ψ(t)]^{1/2}) ≤ α} → Φ(α)` (5·4·2)."

**Formalization Note** `σ > 0` is implicit in the paper (it divides by `σ`). No independence
between `m_t` and the `y_i` is assumed. `y 0` is unused; the sequence is `y 1, y 2, …`.
`Φ` is the distribution function of the standard normal law, `cdf (gaussianReal 0 1)`, and the
convergence is asserted for every real `α`. -/
theorem theorem_B {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : ℝ → ℝ) (hψ_mono : Monotone ψ) (hψ_unbdd : ¬ BddAbove (Set.range ψ))
    (m : ℝ → Ω → ℕ) (hm_meas : ∀ t, Measurable (m t)) (hm_pos : ∀ t ω, 1 ≤ m t ω)
    (hm_ratio : TendstoInMeasure P (fun t ω => (m t ω : ℝ) / ψ t) atTop (fun _ => 1))
    (y : ℕ → Ω → ℝ) (hy_indep : iIndepFun (fun i => y (i + 1)) P)
    (hy_ident : ∀ i, IdentDistrib (y (i + 1)) (y 1) P P)
    (hy_L2 : MemLp (y 1) 2 P) (hy_mean : ∫ ω, y 1 ω ∂P = 0)
    (σ : ℝ) (hσ_pos : 0 < σ) (hy_var : variance (y 1) P = σ ^ 2) :
    ∀ α : ℝ, Tendsto
      (fun t : ℝ => P.real {ω | (∑ i ∈ Finset.Icc 1 (m t ω), y i ω) / (σ * Real.sqrt (ψ t)) ≤ α})
      atTop (𝓝 (cdf (gaussianReal 0 1) α)) := by sorry

end SmithRegenerative.CLT
