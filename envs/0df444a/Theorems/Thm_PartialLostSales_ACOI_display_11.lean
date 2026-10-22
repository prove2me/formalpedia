-- Prove2me | Theorems.Thm_PartialLostSales_ACOI_display_11
-- name    : PartialLostSales.ACOI.display_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:06.324977+00:00
-- url     : https://prove2.me/theorems/0bbac0ee-a7ed-4554-9f29-a7ab4130fefa
-- title:
--   (11), p. 13 — sup_{α∈[α∗,1)} u_α(δ0) < ∞ for the lost-sales COMDP
-- statement:
--   Consider the COMDP of the lost-sales inventory model observed only at zero, under the standing assumptions. Let $u_\alpha(z)=v_\alpha(z)-m_\alpha$ be its relative discounted value function, where $m_\alpha=\inf_z v_\alpha(z)$ and the infimum runs over beliefs with finite second moment. Then there is $\alpha_*\in(0,1)$ such that
--   $$\sup_{\alpha\in[\alpha_*,1)}u_\alpha(\delta_0)<\infty .$$
--
--   This is Assumption B(ii) at the single state $\delta_0$. The paper observes that it implies B(ii) at every belief with finite second moment, because ordering nothing until the inventory hits $0$ costs a bounded amount.
--
--   **Formalization Note.** $u_\alpha$ is computed with truncated subtraction in $[0,\infty]$. This agrees with the paper's difference because $m_\alpha\le v_\alpha(\delta_0)<\infty$ in this model.
-- source:
--   Bai, Chen & Stolyar, Average Cost Optimality in Partially Observed Lost-Sales Inventory Systems, SSRN preprint 3865728, p. 13, display (11)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
import Definitions.Def_PartialLostSales_ACOI_Model

open MeasureTheory ProbabilityTheory Filter Topology FeinbergLiang.ACOE
open scoped ENNReal NNReal

namespace PartialLostSales.ACOI

/-- Display (11), p. 13: there is `α* ∈ (0, 1)` with `sup_{α ∈ [α*, 1)} u_α(δ₀) < ∞`. -/
theorem display_11 (P : Params) (hP : Standing P) (M : MDP (Bel P) (Act P))
    (hM : IsCOMDP P M) :
    ∃ αstar ∈ Set.Ioo (0 : ℝ) 1, (⨆ α ∈ Set.Ico αstar 1, uRel M α (δ0 P)) ≠ ⊤ := by sorry

end PartialLostSales.ACOI
