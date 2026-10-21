-- Prove2me | Theorems.Thm_RegretPricing_Structure_lemma_1
-- name    : RegretPricing.Structure.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:32.682828+00:00
-- url     : https://prove2.me/theorems/4f6f91b2-0429-4a87-b8a9-b00d8c1611ca
-- title:
--   Lemma 1, p. 5 — r_o increases in p, r_u decreases in p, and r_u(p,z) = 0 for p ≥ p∗
-- statement:
--   Let the willingness-to-pay law satisfy the standing assumptions of §2 and IFR, let $0\le z\le b$, and let $p^*$ be a maximizer of $\pi(\cdot,z)$. Then
--
--   1. the overpricing regret $r_o(p,z)=\sup_{y<p}(y-z)[\bar F(y)-\bar F(p)]$ is non-decreasing in $p$;
--   2. the underpricing regret $r_u(p,z)=\sup_{y\ge p}\pi(y,z)-\pi(p,z)$ is non-increasing in $p$;
--   3. $$r_u(p,z)=0\quad\text{for every }p\ge p^*.$$
--
--   The lemma says that a higher price makes overpricing regret larger and underpricing regret smaller, and that above the unbiased optimum there is no underpricing regret at all.
--
--   **Formalization Note.** The paper's derivative signs $\partial r_o/\partial p\ge0$, $\partial r_u/\partial p\le0$ restate "increases"/"decreases" ("that is"); they are formalized as monotonicity, which needs no differentiability.
-- source:
--   Li & Liu, Managerial regret and inventory pricing, accepted manuscript (Management Science, forthcoming; SSRN 3726966), p. 5 (PDF 5), Lemma 1

import Mathlib
import Definitions.Def_RegretPricing_Structure_Model

namespace RegretPricing.Structure

/-- Lemma 1, p. 5: `r_o(p, z)` increases in `p`, `r_u(p, z)` decreases in `p`, and
`r_u(p, z) = 0` whenever `p ≥ p*`. -/
theorem lemma_1 (D : WTP) (hD : D.Standing) (hIFR : D.IFR) (z : ℝ)
    (hz : 0 ≤ z ∧ z ≤ D.b) (pstar : ℝ) (hpstar : IsUnbiasedPrice D z pstar) :
    Monotone (fun p => ro D p z) ∧ Antitone (fun p => ru D p z) ∧
      ∀ p, pstar ≤ p → ru D p z = 0 := by sorry

end RegretPricing.Structure
