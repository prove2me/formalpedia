-- Prove2me | Theorems.Thm_VeinottWagnerSS_RenewalCost_eq9_rAlpha_closed_form
-- name    : VeinottWagnerSS.RenewalCost.eq9_rAlpha_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T13:09:21.603295+00:00
-- url     : https://prove2.me/theorems/5a099459-5e4b-46f1-8a76-8c6632b59415
-- title:
--   Eq. (9) — $r_\alpha(d) = \alpha - (1 - \alpha) M_\alpha(d)$
-- statement:
--   Let $\varphi$ be a demand distribution and $0 \le \alpha \le 1$ with $\alpha\varphi(0) < 1$. For every $d = 0, 1, \dots$, the expected discount factor of the first period in which cumulative demand exceeds $d$,
--   $$r_\alpha(d) = \sum_{i=1}^{\infty} \alpha^i\bigl[\Phi^{i-1}(d) - \Phi^i(d)\bigr],$$
--   equals
--   $$r_\alpha(d) = \alpha - (1 - \alpha) M_\alpha(d).$$
--
--   It expresses the discounted set-up factor through the discount renewal function; in particular $1 - r_\alpha(d) = (1-\alpha)(1 + M_\alpha(d))$.
--
--   **Formalization Note** $r_\alpha$ is defined by the first line of (9), i.e. as $E[\alpha^{T(d)}]$ computed from the law $\Pr[T(d) = i] = \Phi^{i-1}(d) - \Phi^i(d)$.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 533, Eq. (9)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_VeinottWagnerSS_RenewalCost_RenewalFunctions

namespace VeinottWagnerSS.RenewalCost

/-- Veinott & Wagner (1965), Eq. (9), p. 533: under `0 ≤ α ≤ 1` and `α φ(0) < 1`,
`r_α(d) = ∑_{i=1}^{∞} αⁱ [Φ^{i−1}(d) − Φⁱ(d)] = α − (1 − α) M_α(d)` for `d = 0, 1, ⋯`. -/
theorem eq9_rAlpha_closed_form (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hφ0 : α * D.φ 0 < 1) (d : ℕ) :
    rAlpha D.φ α d = α - (1 - α) * MAlpha D.φ α d := by sorry

end VeinottWagnerSS.RenewalCost
