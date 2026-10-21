-- Prove2me | Theorems.Thm_RegretPricing_Structure_step_g
-- name    : RegretPricing.Structure.step_g
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:41.731978+00:00
-- url     : https://prove2.me/theorems/640a2811-7744-48ef-ad15-c938ba292f41
-- title:
--   Step (g), proof of Proposition 4, p. 20 — the overpricing regret r_o(p,z) is non-increasing in z
-- statement:
--   Let the willingness-to-pay law satisfy the standing assumptions of §2. For every price $p$, the overpricing regret
--
--   $$z\longmapsto r_o(p,z)=\sup_{y<p}(y-z)\big[\bar F(y)-\bar F(p)\big]$$
--
--   is non-increasing in the opportunity cost $z$.
--
--   This is the sign fact $\partial r_o(p,z)/\partial z=-[F(p)-F(y(p,z))]\le0$ used in step (g) of the proof of Proposition 4(a).
--
--   **Formalization Note.** Stated in derivative-free form (monotonicity), which is the content of the sign claim.
-- source:
--   Li & Liu, Managerial regret and inventory pricing, accepted manuscript (Management Science, forthcoming; SSRN 3726966), p. 20 (PDF 20), step (g), proof of Proposition 4

import Mathlib
import Definitions.Def_RegretPricing_Structure_Model

namespace RegretPricing.Structure

/-- Step (g), proof of Proposition 4, p. 20: `∂r_o(p, z)/∂z ≤ 0`, i.e. `r_o(p, ·)` is
non-increasing for every price `p`. -/
theorem step_g (D : WTP) (hD : D.Standing) (p : ℝ) :
    Antitone (fun z => ro D p z) := by sorry

end RegretPricing.Structure
