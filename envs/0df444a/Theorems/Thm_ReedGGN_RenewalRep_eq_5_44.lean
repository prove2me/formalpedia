-- Prove2me | Theorems.Thm_ReedGGN_RenewalRep_eq_5_44
-- name    : ReedGGN.RenewalRep.eq_5_44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:26.227321+00:00
-- url     : https://prove2.me/theorems/489ecee7-a8bd-4c9f-946d-59587a16db59
-- title:
--   (5.44) — every càdlàg solution of (5.33) satisfies the dM-representation with drift −β(Fₑ + Fₑ ∗ dM)
-- statement:
--   Let $F$ be a service-time distribution (a probability law $\mu$ on $[0,\infty)$ with mean $1$), $dM$ its renewal measure and $F_e$ its equilibrium distribution. Let $\zeta$ be a càdlàg path on $[0,\infty)$ and $\beta\in\mathbb R$. If $q$ is a càdlàg path solving the limit equation (5.33), $q(t)=\zeta(t)-\beta F_e(t)+\int_0^tq^+(t-s)\,dF(s)$ for $t\ge0$, then for every $t\ge 0$
--   $$q(t)=\zeta(t)+\int_0^t\zeta(t-u)\,dM(u)-\beta\Bigl(F_e(t)+\int_0^tF_e(t-s)\,dM(s)\Bigr)-\int_0^t q^-(t-u)\,dM(u),$$
--   where $q^-=\min(q,0)$.
--
--   This is the step of the proof of Corollary 5.2 obtained by applying the renewal-type solution formula (5.43) to $q^+$; combined with the identity $F_e+F_e*dM=t$ it gives (5.45), i.e. (5.41).
--
--   **Formalization Note** The paper states this for the random limit process $\tilde Q_F$ with $\tilde\zeta=\tilde M_Q+\tilde Q_I$; the statement is pathwise, for a fixed càdlàg driving path. Integrals are over the closed interval $[0,t]$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 30, proof of Corollary 5.2, Eq. (5.44)

import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction
import Definitions.Def_ReedGGN_RenewalRep_Equations

namespace ReedGGN.RenewalRep

open MeasureTheory

/-- (5.44), p. 30: for a service law `μ`, a càdlàg driving path `ζ` and `β ∈ ℝ`, every càdlàg
solution `q` of the limit equation (5.33) satisfies, for every `t ≥ 0`,
`q(t) = ζ(t) + ∫_{[0,t]} ζ(t − u) dM(u) − β (F_e(t) + ∫_{[0,t]} F_e(t − s) dM(s))
  − ∫_{[0,t]} q⁻(t − u) dM(u)`, with `q⁻ = min(q, 0)`. -/
theorem eq_5_44 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1)
    (ζ : ℝ → ℝ) (hζ : ReedGGN.Regulator.IsCadlag ζ) (β : ℝ) (q : ℝ → ℝ) (hq : ReedGGN.Regulator.IsCadlag q)
    (hsol : SolvesLimitEq μ ζ β q) :
    ∀ t : ℝ, 0 ≤ t →
      q t = ζ t + (∫ u in Set.Icc 0 t, ζ (t - u) ∂(renewalMeasure μ))
        - β * (ReedGGN.Regulator.Fe μ t + ∫ s in Set.Icc 0 t, ReedGGN.Regulator.Fe μ (t - s) ∂(renewalMeasure μ))
        - ∫ u in Set.Icc 0 t, min (q (t - u)) 0 ∂(renewalMeasure μ) := by sorry

end ReedGGN.RenewalRep
