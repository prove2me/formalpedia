-- Prove2me | Theorems.Thm_UtilityTokens_ICOChoice_proposition_1
-- name    : UtilityTokens.ICOChoice.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:11.310711+00:00
-- url     : https://prove2.me/theorems/83f31407-992f-4fea-a16c-468cbbfc3528
-- title:
--   Proposition 1, p. 17 — with traditional sales the optimum serves the whole market at p = ((Θ−1)/Θ)x, with payoff ((Θ−1)/Θ)x
-- statement:
--   Let $\Theta\in(1,3]$ and $x>0$. Under traditional sales the entrepreneur chooses a threshold $\bar\theta\in[1,\Theta]$ and earns $X_T(\bar\theta)=p^T_1Q(p^T_1)$. Then:
--
--   1. the maximal profit is attained and equals $\frac{\Theta-1}{\Theta}x$;
--   2. it is attained only at $\bar\theta=1$ (the whole market is served);
--   3. the equilibrium price is $p^T_1=v=\frac{\Theta-1}{\Theta}x$;
--   4. the optimal payoff is
--   $$X^*_T=\frac{\Theta-1}{\Theta}\,x .$$
--
--   Network effects remove the monopolist's incentive to price-discriminate when the spread of types is limited; this is the benchmark against which the ICO is compared.
--
--   **Formalization Note** $X^*_T$ is the supremum of the profit over $\bar\theta\in[1,\Theta]$; the first item pins it as an attained maximum.
-- source:
--   Shakhnov & Zaccaria, Utility Tokens, Network Effects, and Pricing Power, SSRN working paper 3613261 (PDF of 2023-04-23), p. 17, Proposition 1, displays (4)–(6)

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

namespace UtilityTokens.ICOChoice

theorem proposition_1 (Θ x : ℝ) (hΘ1 : 1 < Θ) (hΘ3 : Θ ≤ 3) (hx : 0 < x) :
    IsGreatest (profitT Θ x '' Set.Icc 1 Θ) ((Θ - 1) / Θ * x) ∧
    (∀ θbar ∈ Set.Icc 1 Θ, profitT Θ x θbar = (Θ - 1) / Θ * x → θbar = 1) ∧
    thresholdPrice Θ x 1 = (Θ - 1) / Θ * x ∧
    optPayoffT Θ x = (Θ - 1) / Θ * x := by sorry

end UtilityTokens.ICOChoice
