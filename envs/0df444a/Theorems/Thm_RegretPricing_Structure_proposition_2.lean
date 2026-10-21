-- Prove2me | Theorems.Thm_RegretPricing_Structure_proposition_2
-- name    : RegretPricing.Structure.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:50.297176+00:00
-- url     : https://prove2.me/theorems/ef5e9465-c7bb-4e03-9bba-8acb9f56e36c
-- title:
--   Proposition 2, p. 6 — the regretful seller charges a lower price than the unbiased seller, p̂ ≤ p∗
-- statement:
--   Let the willingness-to-pay law satisfy the standing assumptions of §2 and IFR, let $\alpha,\beta\in[0,1]$, and let $0\le z<b$. If $\hat p$ maximizes $\hat\pi(\cdot,z)$ and $p^*$ maximizes $\pi(\cdot,z)$, then
--
--   $$\hat p\le p^* .$$
--
--   Anticipated regret pushes the price down. The result also gives the identity (15) at the regretful optimum, since $r_u(p,z)=\pi^*(z)-\pi(p,z)$ for $p\le p^*$.
--
--   **Formalization Note.** Posed for $z<b$, where $p^*$ is unique.
-- source:
--   Li & Liu, Managerial regret and inventory pricing, accepted manuscript (Management Science, forthcoming; SSRN 3726966), p. 6 (PDF 6), Proposition 2

import Mathlib
import Definitions.Def_RegretPricing_Structure_Model

namespace RegretPricing.Structure

/-- Proposition 2, p. 6: the regretful seller charges a lower price than the unbiased seller,
`p̂(α, β) ≤ p*` (`z ∈ [0, b)`). -/
theorem proposition_2 (D : WTP) (hD : D.Standing) (hIFR : D.IFR) (α β : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) (z : ℝ) (hz : 0 ≤ z ∧ z < D.b)
    (phat pstar : ℝ) (hphat : IsRegretPrice D α β z phat) (hpstar : IsUnbiasedPrice D z pstar) :
    phat ≤ pstar := by sorry

end RegretPricing.Structure
