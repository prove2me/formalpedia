-- Prove2me | Theorems.Thm_RegretPricing_Structure_proposition_1a
-- name    : RegretPricing.Structure.proposition_1a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:35.073999+00:00
-- url     : https://prove2.me/theorems/903fdb3a-2fd2-4045-8ecd-0e27dcb988ff
-- title:
--   Proposition 1(a), p. 6 — π̂(·,z) has exactly one maximizer p̂, and p̂ = a when h(a)(a − z)[1 + α/(1+β)] > 1
-- statement:
--   Let the willingness-to-pay law satisfy the standing assumptions of §2 and IFR, let $\alpha,\beta\in[0,1]$, and let $0\le z<b$. Then the regretful seller's problem $\max_p\hat\pi(p,z)$ of (4) has exactly one solution $\hat p$, and
--
--   $$h(a)(a-z)\Big[1+\frac{\alpha}{1+\beta}\Big]>1\ \Longrightarrow\ \hat p=a .$$
--
--   This is the existence-and-uniqueness half of Proposition 1(a) together with its corner case; it is what makes "the solution of (4)" and "the solution of (10)" well defined.
--
--   **Formalization Note.** The interior characterization (5) of Proposition 1(a), through the first-order condition and the auxiliary maximizer $y(p,z)$, is not part of this statement. Uniqueness is posed for $z<b$: at $z=b$ every price $p\ge b$ is optimal.
-- source:
--   Li & Liu, Managerial regret and inventory pricing, accepted manuscript (Management Science, forthcoming; SSRN 3726966), p. 6 (PDF 6), Proposition 1(a)

import Mathlib
import Definitions.Def_RegretPricing_Structure_Model

namespace RegretPricing.Structure

/-- Proposition 1(a), p. 6, existence, uniqueness and the corner case: for `z ∈ [0, b)` the
regretful seller's problem (4) has exactly one solution `p̂`, and `p̂ = a` when
`h(a)(a - z)[1 + α/(1 + β)] > 1`. -/
theorem proposition_1a (D : WTP) (hD : D.Standing) (hIFR : D.IFR) (α β : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) (z : ℝ) (hz : 0 ≤ z ∧ z < D.b) :
    (∃! p, IsRegretPrice D α β z p) ∧
      (D.h D.a * (D.a - z) * (1 + α / (1 + β)) > 1 → IsRegretPrice D α β z D.a) := by sorry

end RegretPricing.Structure
