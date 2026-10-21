-- Prove2me | Theorems.Thm_RegretPricing_Structure_regret_price_mono
-- name    : RegretPricing.Structure.regret_price_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:47.250724+00:00
-- url     : https://prove2.me/theorems/4eb3625a-1735-419d-a990-b48f2c9eb386
-- title:
--   Proof of Proposition 4(b), p. 21 — the single-period regretful price p̂(z) increases in z
-- statement:
--   Let the willingness-to-pay law satisfy the standing assumptions of §2 and IFR, and let $\alpha,\beta\in[0,1]$. If $0\le z_1\le z_2<b$, $p_1$ maximizes $\hat\pi(\cdot,z_1)$ and $p_2$ maximizes $\hat\pi(\cdot,z_2)$, then
--
--   $$p_1\le p_2 .$$
--
--   Since $\hat p_t(x)=\hat p(\Delta U_{t-1}(x))$ by (10), this reduces Proposition 4(b) to Proposition 4(a).
-- source:
--   Li & Liu, Managerial regret and inventory pricing, accepted manuscript (Management Science, forthcoming; SSRN 3726966), p. 21 (PDF 21), proof of Proposition 4(b)

import Mathlib
import Definitions.Def_RegretPricing_Structure_Model

namespace RegretPricing.Structure

/-- Proof of Proposition 4(b), p. 21: the regretful price `p̂(z)` increases in the opportunity
cost `z ∈ [0, b)`. -/
theorem regret_price_mono (D : WTP) (hD : D.Standing) (hIFR : D.IFR) (α β : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) (z₁ z₂ : ℝ) (hz₁ : 0 ≤ z₁) (hz₁₂ : z₁ ≤ z₂)
    (hz₂ : z₂ < D.b) (p₁ p₂ : ℝ) (hp₁ : IsRegretPrice D α β z₁ p₁)
    (hp₂ : IsRegretPrice D α β z₂ p₂) :
    p₁ ≤ p₂ := by sorry

end RegretPricing.Structure
