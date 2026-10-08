-- Prove2me | Theorems.Thm_SmithRegenerative_Equilibrium_theorem_1
-- name    : SmithRegenerative.Equilibrium.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:29:57.461084+00:00
-- url     : https://prove2.me/theorems/7ef7cec6-c0a9-423c-8b59-d9c02d1b5aca
-- title:
--   Theorem 1 — the key renewal limit (2·2·3) for bounded, integrable Ψ → 0 when F ∈ 𝔖 and μ₁ < ∞
-- statement:
--   Let $F$ be the law of the renewal intervals (non-negative, not concentrated at $0$), $K$ a delay law on $[0,\infty)$ with $K(+\infty) \le 1$, and $H_K$ the renewal measure. If
--
--   1. $\Psi$ is bounded for $t \ge 0$,
--   2. $\Psi$ is integrable over $(0,\infty)$,
--   3. $\Psi(t) \to 0$ as $t \to \infty$,
--   4. $F \in \mathfrak S$ (some convolution power of $F$ has an absolutely continuous component), and
--   5. $\mu_1 < \infty$,
--
--   then
--   $$
--   \lim_{t\to\infty} \int_0^t \Psi(t-t')\, dH_K(t') = \frac{K(+\infty)}{\mu_1} \int_0^\infty \Psi(t')\, dt'.
--   $$
--
--   Compared with Theorem A, monotonicity of $\Psi$ is replaced by $\Psi \to 0$, at the price of the condition $F \in \mathfrak S$ (which implies $\varpi = 0$). It handles hypothesis (iv)$''_b$ of Theorem 2.
--
--   **Formalization Note** $\Psi$ is assumed measurable, which the paper takes for granted when it integrates $\Psi$ against $H_K$. No aperiodicity hypothesis is added.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 10, Theorem 1, (2·2·3)

import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal

namespace SmithRegenerative.Equilibrium

open MeasureTheory Filter Topology

/-- **Theorem 1** (Smith 1955, §2·2, p. 10). Let `F` be a cycle law and `K` a delay law
(`K(+∞) ≤ 1`), with renewal measure `H_K`. If (i) `Ψ` is bounded for `t ≥ 0`, (ii) `Ψ ∈ L₁(0, ∞)`,
(iii) `lim_{t→∞} Ψ(t) = 0`, (iv) `F ∈ 𝔖` and (v) `μ₁ < ∞`, then
`lim_{t→∞} ∫₀^t Ψ(t − t′) dH_K(t′) = (K(+∞)/μ₁) ∫₀^∞ Ψ(t′) dt′` (2·2·3).

Formalization Note: `Ψ` is measurable (implicit in the paper, which integrates it against `H_K`).
No aperiodicity hypothesis: the paper notes that `F ∈ 𝔖` implies `ϖ = 0`. `μ₁ < ∞` makes
`(mean F).toReal` the paper's `μ₁`, which is positive because `F ≠ δ₀`. -/
theorem theorem_1 (F K : Measure ℝ) (hF : IsCycleLaw F) (hK : IsDelayLaw K)
    (Ψ : ℝ → ℝ) (hΨm : Measurable Ψ)
    (hbdd : ∃ C : ℝ, ∀ v : ℝ, 0 ≤ v → |Ψ v| ≤ C)
    (hint : IntegrableOn Ψ (Set.Ioi 0))
    (hlim : Tendsto Ψ atTop (𝓝 0))
    (hS : InClassS F) (hμ : mean F < ⊤) :
    Tendsto (fun t : ℝ => ∫ s in Set.Icc 0 t, Ψ (t - s) ∂(renewalMeasure K F)) atTop
      (𝓝 ((K Set.univ).toReal / (mean F).toReal * ∫ v in Set.Ioi 0, Ψ v)) := by sorry

end SmithRegenerative.Equilibrium
