-- Prove2me | Theorems.Thm_UtilityTokens_ICOChoice_appendix_a_F_increasing
-- name    : UtilityTokens.ICOChoice.appendix_a_F_increasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:15.928567+00:00
-- url     : https://prove2.me/theorems/85129c8c-2a46-48a6-ae96-2af14ad61359
-- title:
--   Appendix A, p. 35 — F has positive derivative and is strictly increasing for Θ > Θ̃
-- statement:
--   Let $\theta^*$ be given by (11), $\tilde\Theta=(\sqrt5+3)/2$ and
--   $$F(\Theta)=(\theta^*-1)\Bigl[\Bigl(\frac{\Theta-\theta^*}{\Theta}\Bigr)^2-\frac1\Theta\Bigr].$$
--   At every $\Theta>\tilde\Theta$, $F$ has a positive derivative; consequently it is strictly increasing on $(\tilde\Theta,\infty)$.
--
--   Since $\bar x=f/F(\Theta)$ with $f>0$, this is what makes the threshold $\bar x$ decrease in $\Theta$.
--
--   **Formalization Note** The derivative is stated through `HasDerivAt` with an existential value and a positivity condition. The printed formula for $\partial F/\partial\Theta$ omits a factor $1/\Theta$ on the term $2(\Theta-\theta^*)(\theta^*/\Theta-\partial\theta^*/\partial\Theta)$, which does not affect its sign; that incorrect equality is not formalized. The appendix puts no upper bound on $\Theta$, so none is assumed.
-- source:
--   Shakhnov & Zaccaria, Utility Tokens, Network Effects, and Pricing Power, SSRN working paper 3613261 (PDF of 2023-04-23), p. 35, Appendix A

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

namespace UtilityTokens.ICOChoice

theorem appendix_a_F_increasing :
    (∀ Θ : ℝ, thetaTilde < Θ →
      ∃ d : ℝ, HasDerivAt Fden d Θ ∧ 0 < d) ∧
    StrictMonoOn Fden (Set.Ioi thetaTilde) := by sorry

end UtilityTokens.ICOChoice
