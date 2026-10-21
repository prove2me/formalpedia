-- Prove2me | Theorems.Thm_RegretPricing_Structure_eq_15
-- name    : RegretPricing.Structure.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:36.645052+00:00
-- url     : https://prove2.me/theorems/90f6d3c7-64db-45d3-ba4b-d603561dcec7
-- title:
--   (15), p. 20, corrected — π̂ = (1 + β)π − αr_o − βπ∗ for p ≤ p∗, and the maxima over p agree
-- statement:
--   Let the willingness-to-pay law satisfy the standing assumptions of §2 and IFR, let $\alpha,\beta\in[0,1]$, $0\le z<b$, and let $p^*$ maximize $\pi(\cdot,z)$. Then
--
--   1. for every price $p\le p^*$,
--   $$\hat\pi(p,z)=(1+\beta)\pi(p,z)-\alpha r_o(p,z)-\beta\pi^*(z);$$
--   2. $$\max_p\hat\pi(p,z)=\sup_p\Big[(1+\beta)\pi(p,z)-\alpha r_o(p,z)-\beta\pi^*(z)\Big].$$
--
--   The second form is what step (e) of the proof of Proposition 4(a) uses.
--
--   **Formalization Note.** The paper writes (15) for every $p$, "which follows from (4) and Proposition 2". For $p>p^*$ the identity is false in general: there $r_u(p,z)=0$ while $\pi^*(z)-\pi(p,z)>0$. The statement keeps the identity on $p\le p^*$ and adds the equality of the maxima, which is the form the proof needs.
-- source:
--   Li & Liu, Managerial regret and inventory pricing, accepted manuscript (Management Science, forthcoming; SSRN 3726966), p. 20 (PDF 20), (15), proof of Proposition 4 (corrected)

import Mathlib
import Definitions.Def_RegretPricing_Structure_Model

namespace RegretPricing.Structure

/-- (15), proof of Proposition 4, p. 20, corrected: `π̂(p, z) = (1 + β)π(p, z) - α r_o(p, z) - β π*(z)`
holds for every `p ≤ p*`, and the maxima over `p` of both sides agree. -/
theorem eq_15 (D : WTP) (hD : D.Standing) (hIFR : D.IFR) (α β : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) (z : ℝ) (hz : 0 ≤ z ∧ z < D.b)
    (pstar : ℝ) (hpstar : IsUnbiasedPrice D z pstar) :
    (∀ p, p ≤ pstar →
        πhat D α β p z = (1 + β) * revenue D p z - α * ro D p z - β * πstar D z) ∧
      regretValue D α β z =
        ⨆ p : ℝ, ((1 + β) * revenue D p z - α * ro D p z - β * πstar D z) := by sorry

end RegretPricing.Structure
