-- Prove2me | Theorems.Thm_PricingInvCensored_eq_EC16
-- name    : PricingInvCensored.eq_EC16
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:08.302806+00:00
-- url     : https://prove2.me/theorems/b805b37d-e505-4a10-917e-0b3d2739c955
-- title:
--   Eq. (EC.16): accurate difference estimates keep $p^*$ in every trisection interval $[L_\zeta,U_\zeta]$
-- statement:
--   Assume Assumptions 1 and 2, with clairvoyant price $p^*$. Let $[L_0,U_0]=[\underline p,\overline p]$ and let $[L_{\zeta+1},U_{\zeta+1}]$ be the trisection update of Algorithm 3 (lines 7–10) driven by real numbers $D_\zeta$: with $\alpha_\zeta=\frac23L_\zeta+\frac13U_\zeta$ and $\beta_\zeta=\frac13L_\zeta+\frac23U_\zeta$, the next interval is $[\alpha_\zeta,U_\zeta]$ if $D_\zeta>0$ and $[L_\zeta,\beta_\zeta]$ otherwise. If, for every $\zeta<Z$,
--   $$\big|D_\zeta-\Delta_G(\alpha_\zeta,\beta_\zeta)\big|\le\frac{s^2}{4}(\beta_\zeta-\alpha_\zeta)^2\qquad\text{(EC.15)},$$
--   where $\Delta_G(\alpha,\beta)=G(\beta)-G(\alpha)$, then
--   $$p^*\in[L_\zeta,U_\zeta]\qquad\text{for every }\zeta\le Z .$$
--
--   This is Step I of the proof of Theorem 1: on the good event the trisection search never discards the optimal price.
--
--   Differences from the source:
--   - reading: (EC.15), derived from Lemmas 1–2 on the event $\mathcal E_3$ → (EC.15) as a hypothesis; reason: Step I uses only (EC.15).
--   - generalization: the estimates $\widehat\Delta_G(\alpha_\zeta,\beta_\zeta)$ of Algorithm 2 and $\zeta\le\zeta^*$ → any real sequence $D_\zeta$ and any $Z$, with (EC.15) for $\zeta<Z$; reason: the induction uses (EC.15) only at $\zeta_0<\zeta^*$, and the source's case is $D_\zeta=\widehat\Delta_G(\alpha_\zeta,\beta_\zeta)$, $Z=\zeta^*$.
--   - encoding: costs $b,h$ and the bound $|f_\mu'(u)|\le K$ of Assumption 1, and $s^2$ of Assumption 2 → $b\ge0$, $h>0$, $f_\mu$ differentiable at every $u$ of the band, and $s^2$ with $s>0$; reason: $b,h$ are per-unit penalty and holding costs (p. 5), $h>0$ is forced by Assumption 1(3) with compact support, a bound on $f_\mu'(u)$ presupposes the derivative, and only $s^2$ enters.
-- source:
--   Chen, Wang & Zhou, Optimal Policies for Dynamic Pricing and Inventory Control with Nonparametric Censored Demands, SSRN 3750413 (2022-10-19), Proof of Theorem 1, Eqs. (EC.15)–(EC.16), p.ec7, induction p.ec8; Algorithm 3 lines 7–10, p.18

import Mathlib
import Definitions.Def_PricingInvCensored_Model
import Definitions.Def_PricingInvCensored_Controller

open Set

namespace PricingInvCensored

/-- **Eq. (EC.16)**, Chen, Wang & Zhou, SSRN 3750413 (2022-10-19), p.ec7 (induction on p.ec8).
Under Assumptions 1 and 2, let `[L_ζ, U_ζ]` follow the trisection update of Algorithm 3 (lines 7–10,
p.18) from `[L₀, U₀] = [p̲, p̄]` driven by estimates `D_ζ`. If every epoch `ζ < Z` has
`|D_ζ − Δ_G(α_ζ, β_ζ)| ≤ (s²/4)(β_ζ − α_ζ)²` (Eq. (EC.15)), then `p* ∈ [L_ζ, U_ζ]` for every
`ζ ≤ Z`.

**Formalization Note.** Eq. (EC.15) is the hypothesis, as in Step I; the estimates `D_ζ` are an
arbitrary real sequence. -/
theorem eq_EC16 (I : Instance) (pStar yStar : ℝ) (hA1 : Assumption1 I pStar yStar)
    (hA2 : Assumption2 I) (D L U : ℕ → ℝ) (Z : ℕ) (hL0 : L 0 = I.market.low)
    (hU0 : U 0 = I.market.high)
    (hstep : ∀ ζ : ℕ, (L (ζ + 1), U (ζ + 1)) = trisect (L ζ) (U ζ) (D ζ))
    (hacc : ∀ ζ < Z,
      |D ζ - (G I (trisectBeta (L ζ) (U ζ)) - G I (trisectAlpha (L ζ) (U ζ)))| ≤
        I.s ^ 2 / 4 * (trisectBeta (L ζ) (U ζ) - trisectAlpha (L ζ) (U ζ)) ^ 2) :
    ∀ ζ ≤ Z, pStar ∈ Icc (L ζ) (U ζ) := by sorry

end PricingInvCensored
