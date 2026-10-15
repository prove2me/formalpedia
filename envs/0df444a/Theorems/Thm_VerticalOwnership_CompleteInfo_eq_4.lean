-- Prove2me | Theorems.Thm_VerticalOwnership_CompleteInfo_eq_4
-- name    : VerticalOwnership.CompleteInfo.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:33.890161+00:00
-- url     : https://prove2.me/theorems/89e2082d-3228-429a-a446-a321d4ab2274
-- title:
--   (4), p. 9 — v_r(q^adv, K | μ_i) = r(μ_i + ε̲ + ∫_ε̲^{K−μ_i} F̄) − w(1 − β)(q^adv + ∫_{q^adv−μ_i}^{K−μ_i} F̄) − βcK
-- statement:
--   Let $\beta \in [0,1]$ be the retailer's ownership share in the supplier, $\mu_i \in \{\mu_L, \mu_H\}$, and $0 \le q^{adv} \le K$. Write $\bar F = 1 - F$. Then the retailer's accounting payoff $v_r(q^{adv}, K \mid \mu_i) = \pi_r(q^{adv}, K \mid \mu_i) + \beta\pi_s(K \mid \mu_i, q^{adv})$ equals
--   $$r\Big(\mu_i + \underline{\varepsilon} + \int_{\underline{\varepsilon}}^{K-\mu_i} \bar F(x)\,dx\Big) - w(1-\beta)\Big(q^{adv} + \int_{q^{adv}-\mu_i}^{K-\mu_i} \bar F(x)\,dx\Big) - \beta c K.$$
--
--   The closed form separates the revenue term, the retailer's effective purchasing cost $w(1-\beta)$, and her share $\beta cK$ of the capacity cost.
--
--   **Formalization Note** As in (2), the hypothesis $q^{adv} \le K$ is the model's capacity constraint (p. 7); the supplier term of (4) uses the closed form (2), which needs it.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), p. 9, (4); derivation Appendix E, Proof of equations (2)-(4), p. 42

import Mathlib
import Definitions.Def_VerticalOwnership_CompleteInfo_Setting
open MeasureTheory ProbabilityTheory

namespace VerticalOwnership.CompleteInfo

theorem eq_4 (M : Model) (hM : M.Standing) (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (μ : ℝ) (hμ : μ ∈ ({M.μL, M.μH} : Set ℝ)) (q K : ℝ) (hq : 0 ≤ q) (hqK : q ≤ K) :
    M.vr β μ q K =
      M.r * (μ + M.εlo + ∫ x in M.εlo..K - μ, (1 - cdf M.P x))
        - M.w * (1 - β) * (q + ∫ x in q - μ..K - μ, (1 - cdf M.P x))
        - β * M.c * K := by sorry

end VerticalOwnership.CompleteInfo
