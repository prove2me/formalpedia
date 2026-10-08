-- Prove2me | Theorems.Thm_SmithRegenerative_Ergodic_eq_5_3_4
-- name    : SmithRegenerative.Ergodic.eq_5_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:34.82604+00:00
-- url     : https://prove2.me/theorems/eaf09893-420c-4887-b956-70914a49ab7c
-- title:
--   (5·3·4) — Σ₁^{n_t+1} y_i/(n_t + 1) → κ₁ with probability one (printed ν₁)
-- statement:
--   Let $t_1, t_2, \dots$ be a renewal process with $t_0 = 0$ and $\mu_1 = E t_1 < \infty$, and let $w_t$ be a cumulative process relative to it, with cycle increments $y_n = w_{T_n} - w_{T_{n-1}}$. If $E|y_1| < \infty$ and $\kappa_1 = E y_1$, then, with probability one,
--   $$\lim_{t \to \infty} \frac{\sum_{i=1}^{n_t+1} y_i}{n_t + 1} = \kappa_1 .$$
--
--   This is the strong law of large numbers for the increments, evaluated at the random index $n_t + 1$; combined with the renewal strong law it gives the limit of $w$ along regeneration epochs.
--
--   **Formalization Note** The paper prints the limit as $\nu_1$; that is a misprint for $\kappa_1$ ($\nu_1 = E t_0$ is $0$ here, and the next display of the proof concludes $\kappa_1/\mu_1$). The statement uses $\kappa_1$. The limit is along real $t \to \infty$.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 27, §5·3, proof of Theorem 7, (5·3·4)

import Mathlib
import Definitions.Def_SmithRegenerative_Ergodic_Renewal
import Definitions.Def_SmithRegenerative_Ergodic_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.Ergodic

/-- **(5·3·4)** (Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), §5·3, proof of Theorem 7, p. 27): "But, by the strong law of large
numbers, lim_{t=∞} Σ₁^{n_t+1} y_i/(n_t + 1) = ν₁ (5·3·4) with probability one".

Formalization Note: the printed right-hand side "ν₁" is a misprint for `κ₁ = E y₁`: `ν₁ = E t₀`
(2·1·2) is `0` here, and the next display of the proof concludes `κ₁/μ₁`. The statement uses
`κ₁ = ∫ y₁ dP`. Hypotheses are those in force in the proof of Theorem 7 that the display needs:
a renewal process with `t₀ = 0` and `μ₁ < ∞` (integrability of `t₁`), a cumulative process `w`
(`IsCumulativeProcess`; (C1) read literally, no joint independence of `t` and `y`), and
`E|y₁| < ∞`, stated directly as integrability of `y₁`. The limit is along real `t → ∞`. -/
theorem eq_5_3_4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : ℕ → Ω → ℝ) (w : ℝ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hμ : Integrable (t 1) P) (hcum : IsCumulativeProcess P t w)
    (hκ : Integrable (cycleIncrement t w 1) P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun s : ℝ => (∑ i ∈ Finset.Icc 1 (count t s ω + 1), cycleIncrement t w i ω) /
        ((count t s ω : ℝ) + 1))
      atTop (𝓝 (∫ ω, cycleIncrement t w 1 ω ∂P)) := by sorry

end SmithRegenerative.Ergodic
