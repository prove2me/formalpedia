-- Prove2me | Theorems.Thm_SeqExpDiffusion_corollary_2
-- name    : SeqExpDiffusion.corollary_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:20.489544+00:00
-- url     : https://prove2.me/theorems/848c6211-d44e-4170-b3b7-edbb54fddd3e
-- title:
--   Corollary 2 — exit probability and expected duration of experimentation
-- statement:
--   Let $\tilde\sigma>0$, $0<\underline\delta<\bar\delta<1$, $\delta\in(\underline\delta,\bar\delta)$, and let $\tilde\delta$ be a belief diffusion started at $\delta$. Let $\tau^*=\inf\{t>0:\tilde\delta_t\notin(\underline\delta,\bar\delta)\}$ and $\bar p(\delta)=\mathbb P(\tilde\delta_{\tau^*}=\bar\delta\mid\delta_0=\delta)$. Then
--
--   $$\bar p(\delta)=\frac{\delta-\underline\delta}{\bar\delta-\underline\delta}\qquad\text{and}\qquad\mathbb E[\tau^*]=\bar p(\delta)\,\mathcal T(\bar\delta)+(1-\bar p(\delta))\,\mathcal T(\underline\delta)-\mathcal T(\delta),$$
--
--   where $\mathcal T(\delta):=\frac{2}{\tilde\sigma^2}(2\delta-1)\ln\!\big(\frac{\delta}{1-\delta}\big)$. In particular $\mathbb E[\tau^*]<\infty$.
--
--   The corollary gives the probability that experimentation ends by selecting the right action and the expected length of the experimentation phase.
--
--   **Formalization Note** $\tau^*$ is the pathwise first exit time, with $\inf\emptyset=\infty$; the event $\{\tilde\delta_{\tau^*}=\bar\delta\}$ includes $\tau^*<\infty$; $\mathbb E[\tau^*]$ is the integral of $\tau^*$ with values in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: the thresholds δ̲_ij, δ̄_ij of Proposition 5 → any 0 < δ̲ < δ̄ < 1; reason: the thresholds of Proposition 5 for which δ ∈ (δ̲_ij, δ̄_ij) is possible are one case (when δ̲_ij = 0 or δ̄_ij = 1 the interval is not of this form, and T is unbounded there)
--   - generalization: stopping times of the filtration 𝔽 of the experimentation history (p.8) → every probability space and every filtration for which the driving motion is Brownian; reason: the paper's setting is one instance, so the statement specializes to it
--   - reading: E[τ̃*] → E[τ*], with finiteness asserted; reason: τ̃* is a typo for the τ* defined in the statement; the identity is stated in [0, ∞], so it also asserts finiteness
--   - encoding: σ̃ is a volatility, with no stated sign → σ̃ > 0; reason: the paper uses it silently; only the degenerate σ̃ ≤ 0 is excluded
--   - encoding: conditioning on δ_0 = δ → a solution of (12) started at δ; reason: Lean convention; same quantity
-- source:
--   Araman & Caldentey, Diffusion Approximations for a Class of Sequential Testing Problems, arXiv:2102.07030v3, Corollary 2, p.20; proof, p.52

import Definitions.Def_SeqExpDiffusion_IsBeliefDiffusion
import Definitions.Def_TechBreakthrough_discountedAt

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SeqExpDiffusion

/-- Corollary 2, Araman & Caldentey, *Diffusion Approximations for a Class of Sequential Testing Problems*, arXiv:2102.07030v3, p.20: suppose `δ ∈ (δ̲, δ̄)`, let `τ* = inf{t > 0 : δ̃_t ∉ (δ̲, δ̄)}` and
`p̄(δ) = P(δ̃_τ* = δ̄ | δ_0 = δ)`. Then `p̄(δ) = (δ − δ̲)/(δ̄ − δ̲)` and
`E[τ*] = p̄(δ) 𝒯(δ̄) + (1 − p̄(δ)) 𝒯(δ̲) − 𝒯(δ)`, where `𝒯(δ) := (2/σ̃²)(2δ − 1) ln(δ/(1 − δ))`.

**Formalization Note** Stated for every interval `0 < δ̲ < δ̄ < 1` (the paper's `δ̲_ij`, `δ̄_ij` are
one case) and every solution of (12) started at `δ`. `τ*` is the pathwise first exit time
(`inf ∅ = ∞`), the event `δ̃_τ* = δ̄` includes `τ* < ∞`, and `E[τ*]` is the lower Lebesgue integral of
`τ*` in `[0, ∞]`, so the second identity also asserts `E[τ*] < ∞`. -/
theorem corollary_2 (σ : ℝ) (hσ : 0 < σ) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (δ : ℝ) (hδ : δ ∈ Ioo a b) {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 mΩ) (B X : ℝ≥0 → Ω → ℝ) (hX : IsBeliefDiffusion σ δ P ℱ B X) :
    let τ : Ω → WithTop ℝ≥0 := fun ω =>
      TechBreakthrough.firstTime {t | 0 < t ∧ X t ω ∉ Ioo a b}
    let T : ℝ → ℝ := fun x => 2 / σ ^ 2 * (2 * x - 1) * Real.log (x / (1 - x))
    let pbar : ℝ := (δ - a) / (b - a)
    (P {ω | ∃ t : ℝ≥0, τ ω = t ∧ X t ω = b}).toReal = pbar ∧
      ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P = ENNReal.ofReal (pbar * T b + (1 - pbar) * T a - T δ) := by sorry

end SeqExpDiffusion
