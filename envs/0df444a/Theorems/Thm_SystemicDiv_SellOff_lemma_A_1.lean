-- Prove2me | Theorems.Thm_SystemicDiv_SellOff_lemma_A_1
-- name    : SystemicDiv.SellOff.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:17.713026+00:00
-- url     : https://prove2.me/theorems/6cefeaa3-7fa8-45e9-862b-56b882300b20
-- title:
--   Lemma A.1, p. 38 — the amount bank i must raise is $\lambda_{M,i} w_i (R_i + \ell_i)^-$
-- statement:
--   Let a bank have total assets $w > 0$, leverage $\lambda > 0$ and threshold $\lambda_M \ge \lambda$, $\lambda_M > 0$, and let $\ell = \frac{\lambda_M - \lambda}{(1+\lambda)\lambda_M}$ be its distance to liquidation. Let $R$ be its portfolio return. Then the bank breaches its leverage threshold if and only if $R + \ell < 0$, and the amount it must raise, i.e. the solution $x$ of (2.1) counted only when it liquidates, is
--   $$x \,\mathbf 1_{\{\lambda^{post} > \lambda_M\}} = \lambda_M\, w\, (R + \ell)^-,$$
--   where $u^- = \max(-u, 0)$.
--
--   This closed form turns every cost of the model into an explicit function of the return, and is the starting point of all later computations.
--
--   **Formalization Note.** The liquidation rule is the cross-multiplied form of $\lambda^{post} > \lambda_M$; see the model file.
-- source:
--   Capponi & Weber, Systemic Portfolio Diversification, SSRN 3345399 (version of June 15, 2023), p. 38, Lemma A.1

import Mathlib
import Definitions.Def_SystemicDiv_SellOff_Model

namespace SystemicDiv.SellOff

/-- Lemma A.1, p. 38: under the standing assumptions, bank `i` liquidates exactly when
`R_i + ℓ_i < 0`, and the amount it sells is `x_i = λ_{M,i} w_i (R_i + ℓ_i)^−`. -/
theorem lemma_A_1 (b : Bank) (hb : b.Standing) (R : ℝ) :
    (Liquidates b R ↔ R + b.ell < 0) ∧
      sold b R = b.levM * b.w * max (-(R + b.ell)) 0 := by sorry

end SystemicDiv.SellOff
