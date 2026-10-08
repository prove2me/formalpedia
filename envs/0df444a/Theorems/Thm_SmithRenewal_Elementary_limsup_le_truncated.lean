-- Prove2me | Theorems.Thm_SmithRenewal_Elementary_limsup_le_truncated
-- name    : SmithRenewal.Elementary.limsup_le_truncated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:34:42.252049+00:00
-- url     : https://prove2.me/theorems/53323326-f33d-4401-b2f0-fc72c1b0b5c8
-- title:
--   §1.2, p. 246 — lim sup H(t)/t ≤ lim sup H†(t)/t ≤ {μ₁†}⁻¹ for every Δ > 0
-- statement:
--   Let $(X_i)$ be a renewal process with renewal function $H$, let $\Delta > 0$, and let $H^\dagger$ and $\mu_1^\dagger = \mathbb E\min(X_i,\Delta)$ be the renewal function and the mean lifetime of the truncated process $X_i^\dagger = \min(X_i,\Delta)$. Then
--   $$\limsup_{t\to\infty}\frac{H(t)}{t} \;\le\; \limsup_{t\to\infty}\frac{H^\dagger(t)}{t} \;\le\; \{\mu_1^\dagger\}^{-1}.$$
--
--   No assumption is made on $\mu_1$, which may be infinite. Together with the lower bound and $\mu_1^\dagger \to \mu_1$ as $\Delta \to \infty$, this yields the elementary renewal theorem.
--
--   **Formalization Note** Both inequalities of the chain are asserted; the ratios and the inverse are computed in $[0,\infty]$.
-- source:
--   Smith, Renewal Theory and Its Ramifications, J. R. Statist. Soc. B 20(2):243–283 (1958), DOI 10.1111/j.2517-6161.1958.tb00294.x, §1.2, p. 246, lim sup display

import Mathlib
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SmithRenewal.Elementary

/-- Upper bound through the truncation (Smith, *Renewal Theory and Its Ramifications*, J. R. Statist. Soc. B 20(2):243–283 (1958), §1.2, p. 246, unnumbered display): "Thus we can
also deduce from (1.1) that lim sup_{t=∞} H(t)/t ≤ lim sup_{t=∞} H†(t)/t ≤ {μ₁†}⁻¹."

Formalization Note: both inequalities of the chain are stated, for every `Δ > 0` and **without**
any hypothesis on `μ₁` (it may be `∞`); `H†` and `μ₁†` are `H` and `mu1` of
`trunc Δ X`. Ratios are computed in `[0, ∞]`. -/
theorem limsup_le_truncated {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : IsRenewalProcess P X)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    limsup (fun t : ℝ => H X P t / ENNReal.ofReal t) atTop ≤
        limsup (fun t : ℝ => H (trunc Δ X) P t / ENNReal.ofReal t) atTop ∧
    limsup (fun t : ℝ => H (trunc Δ X) P t / ENNReal.ofReal t) atTop ≤
        (mu1 (trunc Δ X) P)⁻¹ := by sorry

end SmithRenewal.Elementary
