-- Prove2me | Theorems.Thm_ReedGGN_RenewalRep_equilibrium_identity
-- name    : ReedGGN.RenewalRep.equilibrium_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:21.981242+00:00
-- url     : https://prove2.me/theorems/cc39dfa0-1b7d-468d-90e2-1cb1afb88ad6
-- title:
--   Proof of Corollary 5.2, p. 30 — Fₑ(t) + ∫₀ᵗ Fₑ(t − s) dM(s) = t
-- statement:
--   Let $F$ be a service-time distribution (a probability law $\mu$ on $[0,\infty)$ with mean $1$), $F_e(x)=\int_0^x(1-F(u))\,du$ its equilibrium distribution (5.4), and $dM$ its renewal measure. Then
--   $$F_e(t)+\int_0^t F_e(t-s)\,dM(s)=t\qquad\text{for every } t\ge 0.$$
--
--   This identity is what turns the drift $-\beta\bigl(F_e(t)+\int_0^tF_e(t-s)\,dM(s)\bigr)$ of (5.44) into the linear drift $-\beta t$ of (5.41).
--
--   **Formalization Note** The identity uses only that $\mu$ is carried by $[0,\infty)$ with $\mu(\{0\})<1$; the service-law hypotheses of the paper (including mean $1$) are kept, as in the paper's setting. The integral is over the closed interval $[0,t]$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 30, proof of Corollary 5.2 (unnumbered display before (5.45))

import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction

namespace ReedGGN.RenewalRep

open MeasureTheory

/-- Proof of Corollary 5.2, p. 30 (unnumbered display before (5.45)): for a service law `μ`,
`F_e(t) + ∫_{[0,t]} F_e(t − s) dM(s) = t` for every `t ≥ 0`. -/
theorem equilibrium_identity (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1) :
    ∀ t : ℝ, 0 ≤ t →
      ReedGGN.Regulator.Fe μ t + ∫ s in Set.Icc 0 t, ReedGGN.Regulator.Fe μ (t - s) ∂(renewalMeasure μ) = t := by sorry

end ReedGGN.RenewalRep
