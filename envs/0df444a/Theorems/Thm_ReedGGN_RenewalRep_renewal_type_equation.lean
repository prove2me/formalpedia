-- Prove2me | Theorems.Thm_ReedGGN_RenewalRep_renewal_type_equation
-- name    : ReedGGN.RenewalRep.renewal_type_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:44.831549+00:00
-- url     : https://prove2.me/theorems/bf105a93-399e-43d6-bf71-2c8af8cf919e
-- title:
--   (5.42)–(5.43) — r = H + H ∗ dM is the unique locally bounded solution of r = H + r ∗ dF
-- statement:
--   Let $F$ be the distribution function of a probability measure $\mu$ on $[0,\infty)$ with $F(0)=\mu(\{0\})<1$, let $dM=\sum_{n\ge1}\mu^{*n}$ be its renewal measure, and let $H$ be a measurable function bounded on every interval $[0,T]$. Define
--   $$r(t)=H(t)+\int_0^t H(t-u)\,dM(u).\tag{5.43}$$
--   Then:
--
--   1. $r$ is bounded on every interval $[0,T]$;
--   2. $r$ solves the **integral equation of renewal type**
--   $$r(t)=H(t)+\int_0^t r(t-u)\,dF(u)\qquad\text{for } t\ge 0;\tag{5.42}$$
--   3. every measurable function $r'$ bounded on every $[0,T]$ that solves (5.42) coincides with $r$ on $[0,\infty)$.
--
--   This is the solution theory of renewal-type equations that the paper cites from Karlin and Taylor; in the proof of Corollary 5.2 it is applied with $r=\tilde Q_F^+$ and $H=\tilde\zeta-\beta F_e-\tilde Q_F^-$.
--
--   **Formalization Note** The paper prints (5.42) as $r(t)=H(t)+\int_0^t r(t)\,dF(t-u)$; the renewal-type equation, as in Karlin–Taylor and as (5.43) requires, is $r(t)=H(t)+\int_0^t r(t-u)\,dF(u)$, which is what is stated. The paper says "a distribution function"; the statement assumes the hypotheses under which the cited result holds, namely $F$ carried by $[0,\infty)$ with $F(0)<1$ (for $F=\delta_0$ the equation $r=H+r$ has no solution unless $H=0$). "Locally bounded" is made explicit as bounded on every $[0,T]$, and measurability of $H$ and of competing solutions is added so the integrals are meaningful. Integrals are over the closed interval $[0,t]$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 29, proof of Corollary 5.2, Eqs. (5.42)–(5.43) (cited from Karlin–Taylor, A First Course in Stochastic Processes)

import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction

namespace ReedGGN.RenewalRep

open MeasureTheory

/-- (5.42)–(5.43), p. 29 (cited from Karlin–Taylor). Let `F` be the distribution function of a
probability measure `μ` carried by `[0, ∞)` with `F(0) = μ {0} < 1`, and let `H` be measurable
and bounded on every `[0, T]`. Then `r(t) = H(t) + ∫_{[0,t]} H(t − u) dM(u)` (5.43) is bounded
on every `[0, T]`, solves the renewal-type equation `r(t) = H(t) + ∫_{[0,t]} r(t − u) dF(u)` for
`t ≥ 0`, and every measurable solution bounded on every `[0, T]` agrees with it on `[0, ∞)`.
(The paper prints `∫_0^t r(t) dF(t − u)` in (5.42); the corrected form is stated.) -/
theorem renewal_type_equation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hatom : μ {0} < 1)
    (H : ℝ → ℝ) (hHm : Measurable H) (hHb : IsLocallyBounded H) :
    let r : ℝ → ℝ := fun t => H t + ∫ u in Set.Icc 0 t, H (t - u) ∂(renewalMeasure μ)
    IsLocallyBounded r ∧
    (∀ t : ℝ, 0 ≤ t → r t = H t + ∫ u in Set.Icc 0 t, r (t - u) ∂μ) ∧
    (∀ r' : ℝ → ℝ, Measurable r' → IsLocallyBounded r' →
      (∀ t : ℝ, 0 ≤ t → r' t = H t + ∫ u in Set.Icc 0 t, r' (t - u) ∂μ) →
      Set.EqOn r' r (Set.Ici 0)) := by sorry

end ReedGGN.RenewalRep
