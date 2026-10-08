-- Prove2me | Theorems.Thm_SmithRenewal_Elementary_truncated_mean_tendsto
-- name    : SmithRenewal.Elementary.truncated_mean_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:12.806014+00:00
-- url     : https://prove2.me/theorems/decdb788-4316-4028-a2a6-11f6b50f6f7e
-- title:
--   §1.2, p. 247 — μ₁† → μ₁ as Δ → ∞ (including μ₁ = ∞)
-- statement:
--   Let $(X_i)$ be a renewal process with mean lifetime $\mu_1 = \mathbb E X_i \in (0,\infty]$, and for $\Delta \in \mathbb R$ let $\mu_1^\dagger(\Delta) = \mathbb E\min(X_i, \Delta)$ be the mean of the truncated lifetime. Then
--   $$\mu_1^\dagger(\Delta) \longrightarrow \mu_1 \qquad (\Delta \to \infty)$$
--   in $[0,\infty]$; in particular $\mu_1^\dagger(\Delta) \to \infty$ when $\mu_1 = \infty$.
--
--   This is the last step of the proof: letting the truncation level grow closes the gap between the upper bound $\{\mu_1^\dagger\}^{-1}$ and $\mu_1^{-1}$.
--
--   **Formalization Note** Expectations are lower integrals of the positive part, so the statement is meaningful for every real $\Delta$ and the limit is taken in $[0,\infty]$.
-- source:
--   Smith, Renewal Theory and Its Ramifications, J. R. Statist. Soc. B 20(2):243–283 (1958), DOI 10.1111/j.2517-6161.1958.tb00294.x, §1.2, p. 247, choosing Δ arbitrarily large

import Mathlib
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SmithRenewal.Elementary

/-- Letting Δ grow (Smith, *Renewal Theory and Its Ramifications*, J. R. Statist. Soc. B 20(2):243–283 (1958), §1.2, p. 247, unnumbered): "By choosing Δ arbitrarily large we can make
μ₁† as near as we like to μ₁ … It should be evident that the truncation argument we have just
employed also disposes of the case μ₁ = ∞."

Formalization Note: stated as `μ₁† → μ₁` in `[0, ∞]` as `Δ → ∞`, which covers `μ₁ = ∞`
(then `μ₁† → ∞`). -/
theorem truncated_mean_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : IsRenewalProcess P X) :
    Tendsto (fun Δ : ℝ => mu1 (trunc Δ X) P) atTop (𝓝 (mu1 X P)) := by sorry

end SmithRenewal.Elementary
