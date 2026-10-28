-- Prove2me | Theorems.Thm_ValuePersPricing_Deviation_pricing_inequality
-- name    : ValuePersPricing.Deviation.pricing_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:31.562645+00:00
-- url     : https://prove2.me/theorems/de263641-bdbc-4633-9348-213d4da21cb1
-- title:
--   Pricing Inequality, §3.1, p. 9 — F̄(x) ≤ R_SP(F,0)/x for every x > 0
-- statement:
--   Let $V\sim F$ be a valuation with $V\ge 0$ almost surely and finite mean, and let the cost be $c=0$. For every price $x>0$,
--   $$\bar F(x)\le\frac{\mathcal R_{SP}(F,0)}{x},$$
--   where $\bar F(x)=\mathbb P(V\ge x)$ and $\mathcal R_{SP}(F,0)=\sup_p p\,\bar F(p)$.
--
--   The optimal single-price revenue thus controls the tail of the valuation distribution; this pointwise bound drives all the upper bounds of the paper.
--
--   Differences from the source:
--   - encoding: V ∼ F nonnegative with cost 0 → a probability measure ν on ℝ with Market ν 0 (V ≥ 0 a.s., E|V| < ∞); reason: standing assumptions of §2.
-- source:
--   Elmachtoub, Gupta & Hamilton, The Value of Personalized Pricing, SSRN 3127719 (review version, PDF sha256 635e22eb…), p. 9 (PDF 9), §3.1, Pricing Inequality

import Mathlib
import Definitions.Def_ValuePersPricing_Deviation_Model

open MeasureTheory Set Filter Topology

namespace ValuePersPricing.Deviation

/-- The Pricing Inequality (§3.1, p. 9): with zero cost, `F̄(x) ≤ R_SP(F, 0)/x` for every `x > 0`. -/
theorem pricing_inequality (ν : Measure ℝ) (hm : Market ν 0) :
    ∀ x : ℝ, 0 < x → tail ν x ≤ spProfit ν 0 / x := by sorry

end ValuePersPricing.Deviation
