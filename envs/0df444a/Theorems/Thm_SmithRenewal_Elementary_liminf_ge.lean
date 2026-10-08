-- Prove2me | Theorems.Thm_SmithRenewal_Elementary_liminf_ge
-- name    : SmithRenewal.Elementary.liminf_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:03.485604+00:00
-- url     : https://prove2.me/theorems/87465a80-4d32-489b-abb6-ccdb5e2725ca
-- title:
--   §1.2, p. 246 — lim inf H(t)/t ≥ μ₁⁻¹ for μ₁ < ∞
-- statement:
--   Let $(X_i)$ be a renewal process with finite mean lifetime $\mu_1 < \infty$ and renewal function $H(t) = \mathbb E N_t$. Then
--   $$\liminf_{t\to\infty} \frac{H(t)}{t} \ge \mu_1^{-1}.$$
--
--   This is the lower half of the elementary renewal theorem, obtained in the paper from (1.1) and the positivity of the residual lifetime $\zeta_t$.
--
--   **Formalization Note** The paper prints "$\liminf_{t=\infty} H(t)/t = \mu_1^{-1}$"; the argument given there yields only the inequality $\ge$, and equality is the elementary renewal theorem itself, so the inequality is what is stated. The ratio $H(t)/t$ is computed in $[0,\infty]$.
-- source:
--   Smith, Renewal Theory and Its Ramifications, J. R. Statist. Soc. B 20(2):243–283 (1958), DOI 10.1111/j.2517-6161.1958.tb00294.x, §1.2, p. 246, lim inf display after (1.1)

import Mathlib
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SmithRenewal.Elementary

/-- Lower bound (Smith, *Renewal Theory and Its Ramifications*, J. R. Statist. Soc. B 20(2):243–283 (1958), §1.2, p. 246, unnumbered display after (1.1)): "the positivity of ζ_t then
proves at once that lim inf_{t=∞} H(t)/t = μ₁⁻¹", in the case `μ₁ < ∞` of (1.1).

Formalization Note: the printed "=" is a typo for "≥": the argument (`μ₁{1 + H(t)} ≥ t`) gives
only the lower bound, and equality is the elementary renewal theorem itself. The ratio is computed
in `[0, ∞]` as `H(t) / ofReal t`; only large `t` matter. -/
theorem liminf_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : IsRenewalProcess P X)
    (hmu : mu1 X P < ⊤) :
    (mu1 X P)⁻¹ ≤ liminf (fun t : ℝ => H X P t / ENNReal.ofReal t) atTop := by sorry

end SmithRenewal.Elementary
