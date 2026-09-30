-- Prove2me | Theorems.Thm_VeinottWagnerSS_RenewalCost_appendix1_MAlpha_summable
-- name    : VeinottWagnerSS.RenewalCost.appendix1_MAlpha_summable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T13:02:43.997443+00:00
-- url     : https://prove2.me/theorems/adfd5aea-545f-499a-bbf3-31d2146bb9e7
-- title:
--   Appendix §1 — the discount renewal function $M_\alpha(k)$ is finite when $\alpha\varphi(0) < 1$
-- statement:
--   Let $\varphi$ be a demand distribution on $\{0, 1, \dots\}$ with distribution functions $\Phi^i$ of its $i$-fold convolutions, and let $0 \le \alpha \le 1$ with $\alpha\varphi(0) < 1$. Then for every $k = 0, 1, \dots$ the series
--   $$M_\alpha(k) = \sum_{i=1}^{\infty} \alpha^i \Phi^i(k)$$
--   converges (absolutely, since its terms are non-negative).
--
--   The case $\alpha < 1$ is immediate; the content is the undiscounted case $\alpha = 1$, where $\varphi(0) < 1$ is needed. Finiteness of $M_\alpha$ makes the renewal quantities $m_\alpha$, $L_\alpha$ and $r_\alpha$ well defined.
--
--   **Formalization Note** Summability is stated for the sequence $i \mapsto \alpha^{i+1}\Phi^{i+1}(k)$, $i \ge 0$, i.e. the paper's sum over $i \ge 1$.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 546, Appendix §1 (Some Renewal Formulas); stated on p. 533

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_VeinottWagnerSS_RenewalCost_RenewalFunctions

namespace VeinottWagnerSS.RenewalCost

/-- Veinott & Wagner (1965), Appendix §1, p. 546: for `0 ≤ α ≤ 1` with `α φ(0) < 1`, the series
`M_α(k) = ∑_{i=1}^{∞} αⁱ Φⁱ(k)` converges (absolutely: its terms are non-negative) for every
`k = 0, 1, ⋯`. -/
theorem appendix1_MAlpha_summable (D : DemandDist) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hφ0 : α * D.φ 0 < 1) (k : ℕ) :
    Summable (fun i : ℕ => α ^ (i + 1) * cdfPow D.φ (i + 1) k) := by sorry

end VeinottWagnerSS.RenewalCost
