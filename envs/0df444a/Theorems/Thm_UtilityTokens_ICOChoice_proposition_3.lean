-- Prove2me | Theorems.Thm_UtilityTokens_ICOChoice_proposition_3
-- name    : UtilityTokens.ICOChoice.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:16.387363+00:00
-- url     : https://prove2.me/theorems/d5e984fc-6f47-43fc-a361-807c1b52b7f9
-- title:
--   Proposition 3, p. 22 — for Θ ∈ (Θ̃, 3] discriminatory pricing is optimal with the ICO but not with traditional sales
-- statement:
--   Let $\tilde\Theta=(\sqrt5+3)/2$, $\Theta\in(\tilde\Theta,3]$, $x>0$ and $f\in\mathbb R$. Then:
--
--   1. the ICO profit attains its maximum over the ICO strategies $(\bar\theta,p^I_1)$;
--   2. every maximizing ICO strategy discriminates, $\bar\theta>1$;
--   3. every maximizing traditional-sales threshold $\bar\theta\in[1,\Theta]$ is $\bar\theta=1$ (no discrimination).
--
--   In this range the ability to charge two prices makes price discrimination profitable, while with a single price network effects still make it unprofitable.
--
--   **Formalization Note** The paper prints the range as $[\tilde\Theta,3]$. At $\Theta=\tilde\Theta$ Lemma 1 gives $\theta^*=1$, so the ICO does not discriminate there; the statement uses the half-open range $(\tilde\Theta,3]$, where the proposition is true.
-- source:
--   Shakhnov & Zaccaria, Utility Tokens, Network Effects, and Pricing Power, SSRN working paper 3613261 (PDF of 2023-04-23), p. 22, Proposition 3

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

namespace UtilityTokens.ICOChoice

theorem proposition_3 (Θ x f : ℝ) (hΘ : thetaTilde < Θ) (hΘ3 : Θ ≤ 3) (hx : 0 < x) :
    (∃ c ∈ ICOChoices Θ x, ∀ c' ∈ ICOChoices Θ x,
        profitI Θ x f c'.1 c'.2 ≤ profitI Θ x f c.1 c.2) ∧
    (∀ c ∈ ICOChoices Θ x,
        (∀ c' ∈ ICOChoices Θ x, profitI Θ x f c'.1 c'.2 ≤ profitI Θ x f c.1 c.2) → 1 < c.1) ∧
    (∀ θbar ∈ Set.Icc 1 Θ,
        (∀ θ' ∈ Set.Icc 1 Θ, profitT Θ x θ' ≤ profitT Θ x θbar) → θbar = 1) := by sorry

end UtilityTokens.ICOChoice
