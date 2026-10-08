-- Prove2me | Theorems.Thm_SmithRegenerative_CLT_renewal_slln
-- name    : SmithRegenerative.CLT.renewal_slln
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:13.953326+00:00
-- url     : https://prove2.me/theorems/6e9242b4-49f8-4f78-b8d0-b3848796c864
-- title:
--   §5·3, p. 27 — the renewal strong law: n_t/t → 1/μ₁ with probability one
-- statement:
--   Let $t_1, t_2, \dots$ be a renewal process — independent, identically distributed, non-negative random variables with $P\{t_1 = 0\} < 1$ — with $t_0 = 0$, and let $n_t$ be the number of epochs $T_k = t_0 + \dots + t_k$ ($k \ge 0$) in $[0, t]$. If $\mu_1 = E t_1 < \infty$, then with probability one
--   $$\lim_{t \to \infty} \frac{n_t}{t} = \frac{1}{\mu_1}.$$
--
--   This is the strong law of large numbers for renewal processes; it is the step that lets the random number of cycles completed by time $t$ be replaced by the deterministic quantity $t/\mu_1$ in the proofs of Lemma 8 and Theorem 9.
--
--   **Formalization Note** The limit is along the real time $t \to \infty$. $\mu_1 > 0$ follows from the hypotheses.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 27, §5·3, proof of Lemma 8

import Mathlib
import Definitions.Def_SmithRegenerative_CLT_CumulativeProcess

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.CLT

/-- Smith (1955), §5·3, proof of Lemma 8, p. 27 (unnumbered): "It may easily be deduced from
renewal theory (see Doob, 1948) that `n_t/t → μ₁⁻¹` with probability one."

For a renewal process with `t₀ = 0` and `μ₁ = E t₁ < ∞`, `n_t / t → 1/μ₁` almost surely as the
real time `t → ∞`. -/
theorem renewal_slln {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : IsRenewal P τ) (hμ : Integrable (τ 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ => (count τ t ω : ℝ) / t) atTop (𝓝 (mu1 P τ)⁻¹) := by sorry

end SmithRegenerative.CLT
