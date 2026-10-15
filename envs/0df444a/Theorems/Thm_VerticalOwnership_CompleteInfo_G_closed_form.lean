-- Prove2me | Theorems.Thm_VerticalOwnership_CompleteInfo_G_closed_form
-- name    : VerticalOwnership.CompleteInfo.G_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:32.371178+00:00
-- url     : https://prove2.me/theorems/83289d94-0310-4726-8359-181d0844c17d
-- title:
--   Appendix E, Proof of Theorem 1, pp. 43–44 — G(β) = z_r(β)(F⁻¹(z_r(β)) − F⁻¹(z_s)) + (z_r + β(1 − z_r))∫_ε̲^{F⁻¹(z_s)} F − ∫_ε̲^{F⁻¹(z_r(β))} F
-- statement:
--   Let $\beta \in [0,1]$, $\mu_i \in \{\mu_L, \mu_H\}$, and $q^* = \mu_i + F^{-1}(z_r(\beta))$. The retailer's accounting payoff gain from financing the entire capacity rather than accepting the supplier's free capacity,
--   $$G(\beta) = \frac1r\Big(v_r(q^*, q^* \mid \mu_i) - v_r\big(0, \mu_i + F^{-1}(z_s) \mid \mu_i\big)\Big),$$
--   equals
--   $$G(\beta) = z_r(\beta)\big(F^{-1}(z_r(\beta)) - F^{-1}(z_s)\big) + \big(z_r + \beta(1 - z_r)\big)\int_{\underline{\varepsilon}}^{F^{-1}(z_s)} F(x)\,dx - \int_{\underline{\varepsilon}}^{F^{-1}(z_r(\beta))} F(x)\,dx.$$
--   In particular $G(\beta)$ does not depend on the market state $i$.
--
--   The right-hand side is the expression whose sign defines the threshold $\underline\beta$ in (9); this identity ties (9) to the payoffs.
--
--   **Formalization Note** $q^*$ is the maximizer identified in the previous milestone; $G$ is defined with the factor $1/r$ exactly as on p. 43.
-- source:
--   Avinadav, Shamir, Partial Vertical Ownership, Capacity Investment and Information Exchange in a Supply Chain, author manuscript of 2022-06-06 (Management Science, doi:10.1287/mnsc.2023.4673), pp. 43–44, Appendix E, Proof of Theorem 1

import Mathlib
import Definitions.Def_VerticalOwnership_CompleteInfo_Setting
open MeasureTheory ProbabilityTheory

namespace VerticalOwnership.CompleteInfo

theorem G_closed_form (M : Model) (hM : M.Standing) (β : ℝ)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (μ : ℝ) (hμ : μ ∈ ({M.μL, M.μH} : Set ℝ)) :
    M.G β μ (μ + M.Finv (M.zrβ β)) = M.G9 β := by sorry

end VerticalOwnership.CompleteInfo
