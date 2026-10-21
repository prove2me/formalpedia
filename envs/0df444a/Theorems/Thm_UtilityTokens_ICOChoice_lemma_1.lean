-- Prove2me | Theorems.Thm_UtilityTokens_ICOChoice_lemma_1
-- name    : UtilityTokens.ICOChoice.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:15.485672+00:00
-- url     : https://prove2.me/theorems/4297aefa-b738-4e5f-af6b-87a243729331
-- title:
--   Lemma 1, p. 22 — θ* = 1 exactly for Θ ≤ Θ̃ = (√5+3)/2 ∈ (1, 3), and θ* > 1 above it
-- statement:
--   Let $\theta_{\mathrm{int}}(\Theta)=\bigl(2\Theta+1-\sqrt{\Theta^2+\Theta+1}\bigr)/3$, $\theta^*(\Theta)=\max[1,\theta_{\mathrm{int}}(\Theta)]$ as in (11), and
--   $$\tilde\Theta=\frac{\sqrt5+3}{2}\approx 2.62 .$$
--   Then:
--
--   1. $\theta_{\mathrm{int}}(\tilde\Theta)=1$;
--   2. $1<\tilde\Theta<3$;
--   3. $\theta^*(\Theta)=1$ for every $\Theta\in(1,\tilde\Theta]$ (non-discriminatory pricing);
--   4. $\theta^*(\Theta)>1$ for every $\Theta>\tilde\Theta$ (discriminatory pricing);
--   5. $\theta^*$ is weakly increasing in $\Theta$ on $(1,\infty)$.
--
--   The lemma splits the parameter range into the region where the ICO does not discriminate and the region where it does.
--
--   **Formalization Note** The paper states that "there exist a threshold value $\tilde\Theta\in(1,3)$"; the Lean names it, $\tilde\Theta=(\sqrt5+3)/2$, as the text before the lemma does, which is stronger than the existential. The case $\Theta\le\tilde\Theta$ ranges over the standing assumption $\Theta>1$.
-- source:
--   Shakhnov & Zaccaria, Utility Tokens, Network Effects, and Pricing Power, SSRN working paper 3613261 (PDF of 2023-04-23), p. 22, Lemma 1 and the sentence before it

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

namespace UtilityTokens.ICOChoice

theorem lemma_1 :
    thetaInterior thetaTilde = 1 ∧
    (1 < thetaTilde ∧ thetaTilde < 3) ∧
    (∀ Θ : ℝ, 1 < Θ → Θ ≤ thetaTilde → thetaStar Θ = 1) ∧
    (∀ Θ : ℝ, thetaTilde < Θ → 1 < thetaStar Θ) ∧
    MonotoneOn thetaStar (Set.Ioi 1) := by sorry

end UtilityTokens.ICOChoice
