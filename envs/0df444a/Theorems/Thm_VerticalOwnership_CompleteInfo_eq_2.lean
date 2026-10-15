-- Prove2me | Theorems.Thm_VerticalOwnership_CompleteInfo_eq_2
-- name    : VerticalOwnership.CompleteInfo.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:31.814182+00:00
-- url     : https://prove2.me/theorems/82b353ed-6e98-487d-a81a-0a26c84b461f
-- title:
--   (2), p. 8 — π_s(K | μ_i, q^adv) = w(K − ∫_{q^adv−μ_i}^{K−μ_i} F) − cK = w(z_s K − ∫_{q^adv−μ_i}^{K−μ_i} F) for 0 ≤ q^adv ≤ K
-- statement:
--   In the partial-vertical-ownership capacity model, let $\mu_i$ be one of the two mean demands $\mu_L, \mu_H$, and let $0 \le q^{adv} \le K$ be an advance order and a capacity covering it. Then the supplier's expected profit $\pi_s(K \mid \mu_i, q^{adv}) = \mathbb E[w\min(K, \max(\mu_i + \varepsilon, q^{adv})) - cK]$ has the closed form
--   $$\pi_s(K \mid \mu_i, q^{adv}) = w\Big(K - \int_{q^{adv}-\mu_i}^{K-\mu_i} F(x)\,dx\Big) - cK = w\Big(z_s K - \int_{q^{adv}-\mu_i}^{K-\mu_i} F(x)\,dx\Big),$$
--   where $F$ is the CDF of the demand shock and $z_s = 1 - c/w$.
--
--   This identity is the basis of every capacity and payoff computation in the paper.
--
--   **Formalization Note** The hypothesis $q^{adv} \le K$ is the model's constraint that capacity covers the advance order (p. 7); the closed form fails without it. $q^{adv} \ge 0$ is the model's domain of advance orders.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), p. 8, (2); derivation Appendix E, Proof of equations (2)-(4), p. 42

import Mathlib
import Definitions.Def_VerticalOwnership_CompleteInfo_Setting
open MeasureTheory ProbabilityTheory

namespace VerticalOwnership.CompleteInfo

theorem eq_2 (M : Model) (hM : M.Standing) (μ : ℝ) (hμ : μ ∈ ({M.μL, M.μH} : Set ℝ))
    (q K : ℝ) (hq : 0 ≤ q) (hqK : q ≤ K) :
    M.πs μ q K = M.w * (K - ∫ x in q - μ..K - μ, cdf M.P x) - M.c * K ∧
      M.πs μ q K = M.w * (M.zs * K - ∫ x in q - μ..K - μ, cdf M.P x) := by sorry

end VerticalOwnership.CompleteInfo
