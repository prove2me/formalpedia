-- Prove2me | Theorems.Thm_SmithRegenerative_Ergodic_count_div_tendsto
-- name    : SmithRegenerative.Ergodic.count_div_tendsto
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:05.208585+00:00
-- url     : https://prove2.me/theorems/884863ac-334f-4f6c-9f3d-6a6550f7cfca
-- title:
--   §5·3, proof of Lemma 8 — the renewal strong law n_t/t → 1/μ₁ with probability one
-- statement:
--   Let $t_1, t_2, \dots$ be a renewal process: independent, identically distributed, non-negative random variables with $P\{t_1 = 0\} < 1$. Let $t_0 = 0$, $T_k = t_1 + \dots + t_k$, and let $n_t = \#\{k \ge 0 : T_k \le t\}$ be the number of regenerations in $[0,t]$. If $\mu_1 = E t_1 < \infty$, then, with probability one,
--   $$\lim_{t \to \infty} \frac{n_t}{t} = \frac{1}{\mu_1}.$$
--
--   This is the renewal-theoretic strong law the paper quotes from Doob (1948). It converts statements indexed by the number of cycles into statements indexed by time, and is used in Lemma 8 and in Theorem 7.
--
--   **Formalization Note** The limit is taken along real $t \to \infty$. The hypothesis $P\{t_1 = 0\} < 1$ implies $\mu_1 > 0$; positivity is not assumed separately.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 27, §5·3, proof of Lemma 8 (unnumbered)

import Mathlib
import Definitions.Def_SmithRegenerative_Ergodic_Renewal

open MeasureTheory ProbabilityTheory Filter Topology

namespace SmithRegenerative.Ergodic

/-- **Renewal strong law** (Smith, *Regenerative stochastic processes*, Proc. R. Soc. Lond. A
232(1188):6–31 (1955), §5·3, proof of Lemma 8, p. 27, unnumbered): "It may easily be deduced
from renewal theory (see Doob, 1948) that n_t/t → μ₁⁻¹ with probability one."

The context of the sentence is Lemma 8: `t₀ = 0` and `μ₁ = E t₁ < ∞`.

Formalization Note: `t` is a renewal process (`IsRenewalProcess`: `t₁, t₂, …` i.i.d.,
non-negative, `P{t₁ = 0} < 1`) with delay `t₀ = 0` at every sample point; `μ₁ < ∞` is
integrability of `t₁`, and `μ₁ = ∫ t₁ dP`, which is strictly positive under the hypotheses (it
is not assumed separately). `n_t` is `count t t ω`, the number of `k ≥ 0` with `T_k ≤ t`. The
limit is along real `t → ∞`. -/
theorem count_div_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (t : ℕ → Ω → ℝ) (hren : IsRenewalProcess P t)
    (ht0 : ∀ ω, t 0 ω = 0) (hμ : Integrable (t 1) P) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => (count t s ω : ℝ) / s) atTop
      (𝓝 (∫ ω, t 1 ω ∂P)⁻¹) := by sorry

end SmithRegenerative.Ergodic
