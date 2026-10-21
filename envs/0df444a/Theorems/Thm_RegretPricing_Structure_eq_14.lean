-- Prove2me | Theorems.Thm_RegretPricing_Structure_eq_14
-- name    : RegretPricing.Structure.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:37.075992+00:00
-- url     : https://prove2.me/theorems/76431727-941c-4937-9eb2-f2b85326a118
-- title:
--   (14), proof of Proposition 4, p. 20 — dπ∗(z)/dz = −F̄(p∗(z)) ≤ 0
-- statement:
--   Let the willingness-to-pay law satisfy the standing assumptions of §2 and IFR, and let $\pi^*(z)=\max_p(p-z)\bar F(p)$. Then for every $z\in[0,b)$ and the unbiased optimal price $p^*(z)$, $\pi^*$ is differentiable at $z$ with
--
--   $$\frac{d\pi^*(z)}{dz}=-\bar F\big(p^*(z)\big)\le 0,$$
--
--   and $\pi^*$ is non-increasing on $[0,b]$.
--
--   This envelope identity is used in steps (h) and (i) of the proof of Proposition 4(a).
-- source:
--   Li & Liu, Managerial regret and inventory pricing, accepted manuscript (Management Science, forthcoming; SSRN 3726966), p. 20 (PDF 20), (14), proof of Proposition 4

import Mathlib
import Definitions.Def_RegretPricing_Structure_Model

namespace RegretPricing.Structure

/-- (14), proof of Proposition 4, p. 20: `dπ*(z)/dz = -F̄(p*(z)) ≤ 0`; in particular `π*` is
non-increasing on `[0, b]`. -/
theorem eq_14 (D : WTP) (hD : D.Standing) (hIFR : D.IFR) :
    (∀ z ∈ Set.Ico 0 D.b, ∀ p, IsUnbiasedPrice D z p → HasDerivAt (πstar D) (-(D.Fbar p)) z) ∧
      AntitoneOn (πstar D) (Set.Icc 0 D.b) := by sorry

end RegretPricing.Structure
