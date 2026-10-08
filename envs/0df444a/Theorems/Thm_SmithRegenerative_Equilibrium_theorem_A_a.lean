-- Prove2me | Theorems.Thm_SmithRegenerative_Equilibrium_theorem_A_a
-- name    : SmithRegenerative.Equilibrium.theorem_A_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:02.979764+00:00
-- url     : https://prove2.me/theorems/4723f731-2818-44df-bc1c-771b012557ba
-- title:
--   Theorem A(a) — the key renewal theorem: ∫₀^t Ψ(t − t′)dH_K(t′) → (K(+∞)/μ₁)∫₀^∞Ψ for bounded non-increasing integrable Ψ, ϖ = 0
-- statement:
--   Let $F$ be the law of the renewal intervals (non-negative, not concentrated at $0$) with mean $\mu_1 \in (0,\infty]$, let $K$ be a delay law on $[0,\infty)$ with total mass $K(+\infty) \le 1$, and let $H_K$ be the renewal measure. Suppose $F$ is aperiodic ($\varpi = 0$). If $\Psi$ is
--
--   1. bounded and non-increasing in $(0,\infty)$, and
--   2. integrable over $(0,\infty)$,
--
--   then
--   $$
--   \lim_{t\to\infty} \int_0^t \Psi(t-t')\, dH_K(t') = \frac{K(+\infty)}{\mu_1} \int_0^\infty \Psi(t')\, dt',
--   $$
--   where the right-hand side is $0$ if $\mu_1 = \infty$.
--
--   This is the key renewal theorem in the form Smith (1954) proved it; it is the basis of the limit theorem for equilibrium processes. Part (b) of the paper's Theorem A, for periodic $F$, is not part of this statement.
--
--   **Formalization Note** The cases $\mu_1 = \infty$ (limit $0$) and $\mu_1 < \infty$ are stated as two separate conclusions. $\Psi$ is a measurable function on $\mathbb R$ bounded on $[0,\infty)$; only its values on $[0,\infty)$ enter. The integral over $[0,t]$ is closed at both ends.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 10, Theorem A(a), (2·2·1)

import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal

namespace SmithRegenerative.Equilibrium

open MeasureTheory Filter Topology

/-- **Theorem A(a)** (Smith 1955, §2·2, p. 10; the key renewal theorem, quoted from Smith 1954).
Let `F` be a cycle law and `K` a delay law (`K(+∞) ≤ 1`), with renewal measure
`H_K = Σ_{n ≥ 0} K ∗ F^{∗n}`. If `ϖ = 0` (`F` aperiodic) and `Ψ` is (i) bounded and non-increasing in
`(0, ∞)` and (ii) in `L₁(0, ∞)`, then
`lim_{t→∞} ∫₀^t Ψ(t − t′) dH_K(t′) = (K(+∞)/μ₁) ∫₀^∞ Ψ(t′) dt′` (2·2·1),
where the right-hand side is zero if `μ₁ = ∞`. Part (b) (periodic `F`) is not stated.

Formalization Note: the two cases `μ₁ = ∞` and `μ₁ < ∞` are stated separately. `Ψ` is a measurable
function on `ℝ` (the paper's `Ψ` lives on `[0, ∞)` and is integrated; only its values on `[0, ∞)`
enter). Boundedness is on `[0, ∞)`; the value `Ψ(0)` enters through atoms of `H_K` at `t`. The
Stieltjes integral `∫₀^t … dH_K(t′)` is over the closed interval `[0, t]`. -/
theorem theorem_A_a (F K : Measure ℝ) (hF : IsCycleLaw F) (hK : IsDelayLaw K)
    (hper : IsAperiodic F) (Ψ : ℝ → ℝ) (hΨm : Measurable Ψ)
    (hbdd : ∃ C : ℝ, ∀ v : ℝ, 0 ≤ v → |Ψ v| ≤ C)
    (hmono : AntitoneOn Ψ (Set.Ioi 0)) (hint : IntegrableOn Ψ (Set.Ioi 0)) :
    (mean F = ⊤ →
      Tendsto (fun t : ℝ => ∫ s in Set.Icc 0 t, Ψ (t - s) ∂(renewalMeasure K F)) atTop (𝓝 0)) ∧
    (mean F ≠ ⊤ →
      Tendsto (fun t : ℝ => ∫ s in Set.Icc 0 t, Ψ (t - s) ∂(renewalMeasure K F)) atTop
        (𝓝 ((K Set.univ).toReal / (mean F).toReal * ∫ v in Set.Ioi 0, Ψ v))) := by sorry

end SmithRegenerative.Equilibrium
