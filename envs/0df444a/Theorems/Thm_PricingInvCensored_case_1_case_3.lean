-- Prove2me | Theorems.Thm_PricingInvCensored_case_1_case_3
-- name    : PricingInvCensored.case_1_case_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:04.54876+00:00
-- url     : https://prove2.me/theorems/10609416-ed9f-4e48-85f6-421fa4948464
-- title:
--   Proof of Theorem 1, Step I, Cases 1 and 3: $p^*<\alpha\Rightarrow G(\beta)-G(\alpha)\le-\frac{s^2}{2}(\beta-\alpha)^2$, and symmetrically
-- statement:
--   Assume Assumptions 1 and 2, with clairvoyant price $p^*$, and let $\underline p\le\alpha<\beta\le\overline p$. Write $\Delta_G(\alpha,\beta)=G(\beta)-G(\alpha)$.
--   1. (Case 1) If $p^*<\alpha$, then $$\Delta_G(\alpha,\beta)\le-\frac{s^2}{2}(\beta-\alpha)^2 .$$
--   2. (Case 3) If $p^*>\beta$, then $$\Delta_G(\alpha,\beta)\ge\frac{s^2}{2}(\beta-\alpha)^2 .$$
--
--   Strong concavity makes the sign of the reward difference at the two trisection points reveal on which side of them $p^*$ lies, with a margin of order $(\beta-\alpha)^2$.
--
--   Differences from the source:
--   - generalization: the trisection points $\alpha_{\zeta_0},\beta_{\zeta_0}$ of $[L_{\zeta_0},U_{\zeta_0}]$ with $p^*\in[L_{\zeta_0},\alpha_{\zeta_0})$ → any $\underline p\le\alpha<\beta\le\overline p$ with $p^*<\alpha$; reason: the argument uses only Assumption 2 and the interior optimum, and the source's case is $\alpha=\alpha_{\zeta_0}$, $\beta=\beta_{\zeta_0}$.
--   - reading: Case 3 "by symmetry, this case can be dealt with similarly as in Case 1" → $\Delta_G(\alpha,\beta)\ge\frac{s^2}{2}(\beta-\alpha)^2$ when $p^*>\beta$; reason: this is Case 1's inequality with the roles of the endpoints exchanged, which is what the induction for (EC.16) uses.
--   - encoding: costs $b,h$ and the bound $|f_\mu'(u)|\le K$ of Assumption 1, and $s^2$ of Assumption 2 → $b\ge0$, $h>0$, $f_\mu$ differentiable at every $u$ of the band, and $s^2$ with $s>0$; reason: $b,h$ are per-unit penalty and holding costs (p. 5), $h>0$ is forced by Assumption 1(3) with compact support, a bound on $f_\mu'(u)$ presupposes the derivative, and only $s^2$ enters.
-- source:
--   Chen, Wang & Zhou, Optimal Policies for Dynamic Pricing and Inventory Control with Nonparametric Censored Demands, SSRN 3750413 (2022-10-19), Proof of Theorem 1, Step I, Case 1 and Case 3, p.ec8

import Mathlib
import Definitions.Def_PricingInvCensored_Model

open Set

namespace PricingInvCensored

/-- **Proof of Theorem 1, Step I, Case 1 and Case 3**, Chen, Wang & Zhou, SSRN 3750413
(2022-10-19), p.ec8. Under Assumptions 1 and 2, for prices `p̲ ≤ α < β ≤ p̄`: if `p* < α` then
`Δ_G(α, β) = G(β) − G(α) ≤ −(s²/2)(β − α)²`, and if `p* > β` then
`G(β) − G(α) ≥ (s²/2)(β − α)²`.

**Formalization Note.** Stated for every `α < β` in the price range (the proof does not use that
they are trisection points); Case 3 is the "by symmetry" counterpart of Case 1. -/
theorem case_1_case_3 (I : Instance) (pStar yStar : ℝ) (hA1 : Assumption1 I pStar yStar)
    (hA2 : Assumption2 I) (α β : ℝ) (hα : I.market.low ≤ α) (hαβ : α < β)
    (hβ : β ≤ I.market.high) :
    (pStar < α → G I β - G I α ≤ -(I.s ^ 2 / 2) * (β - α) ^ 2) ∧
      (β < pStar → I.s ^ 2 / 2 * (β - α) ^ 2 ≤ G I β - G I α) := by sorry

end PricingInvCensored
