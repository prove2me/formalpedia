-- Prove2me | Theorems.Thm_TokenFinance_OptToken_lemma_3
-- name    : TokenFinance.OptToken.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:31.215214+00:00
-- url     : https://prove2.me/theorems/17ad5e8a-7935-4fe6-927b-34f38eb95d68
-- title:
--   Lemma 3 and equations (11)–(12): optimal revenue share
-- statement:
--   Let $c>0$ be marginal cost and $t>0$ the number of units pre-sold to investors. Give those investors the fraction $\alpha_t=t/(c+t)$ of the tokens issued after production. Then $0<\alpha_t<1$. For every demand intercept $x$ such that the monopoly quantity $q^m(x)=(x-c)/2$ exceeds $t$, the entrepreneur's time-one payoff from any output $q>t$ is at most her payoff at $q^m(x)$:
--
--   $$(1-\alpha_t)(q-t)(x-q)-cq\le(1-\alpha_t)(q^m(x)-t)(x-q^m(x))-cq^m(x).$$
--
--   This is the incentive calculation behind the contract's revenue share. **Formalization Note** This statement concerns the high-demand case treated before the paper introduces the low-demand refund terms; both quantities range over $q>t$.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), pp. 21–22 (PDF pp. 22–23), Lemma 3 and (11)–(12)

import Mathlib
import Definitions.Def_TokenFinance_Debt_Setting

namespace TokenFinance.OptToken

theorem lemma_3 (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    0 < TokenFinance.Debt.alphaT c t ∧ TokenFinance.Debt.alphaT c t < 1 ∧
      ∀ x q : ℝ, t < (x - c) / 2 → t < q →
        (1 - TokenFinance.Debt.alphaT c t) * (q - t) * (x - q) - c * q ≤
          (1 - TokenFinance.Debt.alphaT c t) * ((x - c) / 2 - t) * (x - (x - c) / 2) -
            c * ((x - c) / 2) := by sorry

end TokenFinance.OptToken
