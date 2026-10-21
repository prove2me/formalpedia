-- Prove2me | Theorems.Thm_RegretPricing_Structure_proposition_4a
-- name    : RegretPricing.Structure.proposition_4a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:42.174988+00:00
-- url     : https://prove2.me/theorems/c856cf19-95ac-4adb-9116-deb098ac7d8f
-- title:
--   Proposition 4(a), p. 10 — ΔU_t(x) increases in the time-to-go t and decreases in the remaining inventory x
-- statement:
--   Let the willingness-to-pay law satisfy the standing assumptions of §2 and IFR, let $\alpha,\beta\in[0,1]$, let the arrival probability satisfy $0\le\lambda\le 1/2$, and assume the paper's regularity condition $\hat m(z,\alpha,\beta)\le0$, i.e. that the optimal regret value $z\mapsto\max_p\hat\pi(p,z)$ is non-increasing on $[0,b]$. Let $U_t(x)$ be the regretful seller's value-to-go (10) and $\Delta U_t(x)=U_t(x)-U_t(x-1)$. Then for all $t\ge0$ and $x\ge1$,
--
--   $$\Delta U_t(x)\le\Delta U_{t+1}(x)\qquad\text{and}\qquad\Delta U_t(x+1)\le\Delta U_t(x).$$
--
--   The marginal value of inventory rises with the time left and falls with the stock on hand, as in the unbiased Bitran–Mondschein model.
--
--   **Formalization Note.** $\hat m$ is the $z$-derivative of the optimal regret value (envelope formula, p. 22), so $\hat m\le0$ on $z\in[0,b]$ is rendered as the optimal regret value being non-increasing on $[0,b]$. The inventory cap $x\le c$ is dropped.
-- source:
--   Li & Liu, Managerial regret and inventory pricing, accepted manuscript (Management Science, forthcoming; SSRN 3726966), p. 10 (PDF 10), Proposition 4(a); regularity assumption p. 6 (PDF 6)

import Mathlib
import Definitions.Def_RegretPricing_Structure_Model

namespace RegretPricing.Structure

/-- Proposition 4(a), p. 10: `ΔU_t(x)` increases in the time-to-go `t` and decreases in the
remaining inventory `x`. -/
theorem proposition_4a (D : WTP) (hD : D.Standing) (hIFR : D.IFR) (α β lam : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) (hlam : 0 ≤ lam ∧ lam ≤ 1 / 2)
    (hm : AntitoneOn (regretValue D α β) (Set.Icc 0 D.b)) :
    (∀ t x : ℕ, 1 ≤ x → dU D α β lam t x ≤ dU D α β lam (t + 1) x) ∧
      (∀ t x : ℕ, 1 ≤ x → dU D α β lam t (x + 1) ≤ dU D α β lam t x) := by sorry

end RegretPricing.Structure
