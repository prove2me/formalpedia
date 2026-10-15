-- Prove2me | Theorems.Thm_VerticalOwnership_CompleteInfo_no_advance_order_dominates
-- name    : VerticalOwnership.CompleteInfo.no_advance_order_dominates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:29.957779+00:00
-- url     : https://prove2.me/theorems/4a0a5404-855d-4f88-8b09-c56cf1b10a85
-- title:
--   §4, p. 10 — a positive advance order up to μ_i + F⁻¹(z_s) leaves K^CI unchanged and is weakly dominated by ordering nothing
-- statement:
--   Let $\beta \in [0,1]$, $\mu_i \in \{\mu_L, \mu_H\}$, and let $0 < q^{adv} \le \mu_i + F^{-1}(z_s)$. Then the advance order does not change the capacity the supplier builds,
--   $$K_i^{CI}(q^{adv}) = K_i^{CI}(0),$$
--   and not ordering in advance is at least as good for the retailer:
--   $$v_r\big(q^{adv}, K_i^{CI}(q^{adv}) \mid \mu_i\big) \le v_r\big(0, K_i^{CI}(0) \mid \mu_i\big).$$
--
--   This reduces the retailer's choice under complete information to the two options compared in (7).
--
--   **Formalization Note** "Dominates" is read as weak dominance: for $\beta < 1$, every advance order $q^{adv} \le \mu_i + \underline\varepsilon$ is always sold and gives exactly the payoff of ordering nothing, so strict dominance would be false.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), p. 10, §4, paragraph after (5)

import Mathlib
import Definitions.Def_VerticalOwnership_CompleteInfo_Setting
open MeasureTheory ProbabilityTheory

namespace VerticalOwnership.CompleteInfo

theorem no_advance_order_dominates (M : Model) (hM : M.Standing) (β : ℝ)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (μ : ℝ) (hμ : μ ∈ ({M.μL, M.μH} : Set ℝ))
    (q : ℝ) (hq : q ∈ Set.Ioc 0 (μ + M.Finv M.zs)) :
    M.KCI μ q = M.KCI μ 0 ∧
      M.vr β μ q (M.KCI μ q) ≤ M.vr β μ 0 (M.KCI μ 0) := by sorry

end VerticalOwnership.CompleteInfo
