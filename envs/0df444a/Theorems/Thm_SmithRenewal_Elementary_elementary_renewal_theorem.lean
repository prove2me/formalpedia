-- Prove2me | Theorems.Thm_SmithRenewal_Elementary_elementary_renewal_theorem
-- name    : SmithRenewal.Elementary.elementary_renewal_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:11.591983+00:00
-- url     : https://prove2.me/theorems/b689ea1a-fac8-4240-8c12-fa8e3e439bae
-- title:
--   §1.2, p. 246 — the elementary renewal theorem: H(t)/t → μ₁⁻¹ as t → ∞ (μ₁ ≤ ∞, limit 0 if μ₁ = ∞)
-- statement:
--   Let $X_1, X_2, \dots$ be a renewal process: independent, identically distributed, non-negative random variables that do not vanish with probability one. Let $S_n = X_1 + \dots + X_n$, let $N_t$ be the number of renewals $n \ge 1$ with $S_n \le t$, let $H(t) = \mathbb E N_t$ be the renewal function and $\mu_1 = \mathbb E X_i \le \infty$ the mean lifetime. Then
--   $$\frac{H(t)}{t} \longrightarrow \mu_1^{-1} \qquad (t \to \infty),$$
--   where the limit $\mu_1^{-1}$ is interpreted as zero if $\mu_1 = \infty$.
--
--   The elementary renewal theorem is the first-order asymptotics of the renewal function: in the long run renewals occur at rate $1/\mu_1$ on average. It underlies long-run average cost and reward computations for renewal and regenerative models in inventory, maintenance and queueing.
--
--   **Formalization Note** $H(t)$ and $\mu_1$ are lower integrals in $[0,\infty]$, the ratio is formed in $[0,\infty]$, and the limit is the inverse in $[0,\infty]$, where $\infty^{-1} = 0$ is exactly the paper's convention. No hypothesis on $\mu_1$, no second moment and no non-lattice condition is assumed.
-- source:
--   Smith, Renewal Theory and Its Ramifications, J. R. Statist. Soc. B 20(2):243–283 (1958), DOI 10.1111/j.2517-6161.1958.tb00294.x, §1.2, p. 246, elementary renewal theorem

import Mathlib
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SmithRenewal.Elementary

/-- The elementary renewal theorem (Smith, *Renewal Theory and Its Ramifications*, J. R. Statist. Soc. B 20(2):243–283 (1958), §1.2, p. 246, unnumbered display): "H(t)/t → μ₁⁻¹ as
t → ∞, where μ₁ = EX_i ≤ ∞, and the limit μ₁⁻¹ is interpreted as zero if μ₁ = ∞."

Formalization Note: `H(t) = E N_t` and `μ₁ = E X_i` are lower integrals in `[0, ∞]`, the ratio
is `H(t) / ofReal t` in `[0, ∞]` and the limit `μ₁⁻¹` is the inverse in `[0, ∞]`, so
`∞⁻¹ = 0` is exactly the paper's convention. No hypothesis on `μ₁` is made (`μ₁ > 0` follows
from `P {X_i = 0} < 1`). -/
theorem elementary_renewal_theorem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : IsRenewalProcess P X) :
    Tendsto (fun t : ℝ => H X P t / ENNReal.ofReal t) atTop (𝓝 (mu1 X P)⁻¹) := by sorry

end SmithRenewal.Elementary
