-- Prove2me | Theorems.Thm_RegretPricing_Structure_unbiased_price_unique
-- name    : RegretPricing.Structure.unbiased_price_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:34.359846+00:00
-- url     : https://prove2.me/theorems/ccc6e106-7511-4070-8048-17599c30ad2f
-- title:
--   §2, p. 4 — under IFR the unbiased optimal price p∗ is unique and π(·,z) is unimodal around it
-- statement:
--   Let the willingness-to-pay law satisfy the standing assumptions of §2 (support $[a,b]$, $0\le a<b<\infty$, density continuous on $[a,b]$) and have an increasing failure rate. Let $0\le z<b$. Then the unbiased seller's revenue $\pi(p,z)=(p-z)\bar F(p)$ has exactly one maximizer $p^*$, and
--
--   $$p\mapsto\pi(p,z)\ \text{is non-decreasing on }(-\infty,p^*]\ \text{and non-increasing on }[p^*,\infty).$$
--
--   This is the unimodality the paper uses throughout: it gives $r_u(p,z)=0$ for $p\ge p^*$ and underlies Proposition 2 and (14).
--
--   **Formalization Note.** The page states uniqueness for $z\in[0,b]$; at $z=b$ every $p\ge b$ attains the maximum value $0$, so the statement is posed for $z<b$, the range visited by the dynamic program. The unimodality conjunct is the first sentence of the proof of Lemma 1, p. 18.
-- source:
--   Li & Liu, Managerial regret and inventory pricing, accepted manuscript (Management Science, forthcoming; SSRN 3726966), p. 4 (PDF 4), §2; proof of Lemma 1, p. 18 (PDF 18)

import Mathlib
import Definitions.Def_RegretPricing_Structure_Model

namespace RegretPricing.Structure

/-- §2, p. 4, and proof of Lemma 1, p. 18: under IFR the unbiased seller has a unique optimal
price `p*`, and `π(·, z)` increases below `p*` and decreases above it (`z ∈ [0, b)`). -/
theorem unbiased_price_unique (D : WTP) (hD : D.Standing) (hIFR : D.IFR) (z : ℝ)
    (hz : 0 ≤ z ∧ z < D.b) :
    (∃! p, IsUnbiasedPrice D z p) ∧
      ∀ p, IsUnbiasedPrice D z p →
        MonotoneOn (fun q => revenue D q z) (Set.Iic p) ∧
          AntitoneOn (fun q => revenue D q z) (Set.Ici p) := by sorry

end RegretPricing.Structure
