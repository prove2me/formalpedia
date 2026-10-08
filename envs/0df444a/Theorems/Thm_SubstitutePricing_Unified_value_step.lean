-- Prove2me | Theorems.Thm_SubstitutePricing_Unified_value_step
-- name    : SubstitutePricing.Unified.value_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:43.158684+00:00
-- url     : https://prove2.me/theorems/08dfc1ee-eaf3-4388-a04b-f5cf19953ed3
-- title:
--   (14) — the unified value equals the sum of period margins at the same inventory
-- statement:
--   Let $t\ge1$ and let $x$ have a nonempty in-stock set. For each $s=1,\dots,t$, let $m_s(x)$ solve the period-$s$ margin equation at the same inventory $x$:
--   $$
--   \left(\frac{m_s(x)}{\mu}-1\right)\exp\left(\frac{m_s(x)+u_0}{\mu}\right)
--   =\exp\left(\frac{a_w-\Delta^w\pi_{s-1}(x)}{\mu}\right).
--   $$
--   Then the maximum expected revenue is the displayed formula (14):
--   $$
--   \pi_t(x)=\lambda\sum_{s=1}^{t}[m_s(x)-\mu].
--   $$
--
--   **Formalization Note.** The value function is the unified-pricing value function. The in-stock hypothesis makes $a_w$ and the weighted marginal value meaningful. The statement quantifies over every family of roots, which uniquely determines each $m_s(x)$.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 337, App. A, proof of Proposition 1

import Mathlib
import Definitions.Def_SubstitutePricing_Unified_Model

namespace SubstitutePricing.Unified

theorem value_step (M : Model) (hM : M.Assumptions) (t : ℕ) (ht : 1 ≤ t)
    (x : Fin M.n → ℕ) (hx : (M.S x).Nonempty) :
    ∀ ms : ℕ → ℝ,
      (∀ s ∈ Finset.Icc 1 t, M.marginLHS (ms s) = M.sigmaU s x) →
      M.piU t x = M.lam * ∑ s ∈ Finset.Icc 1 t, (ms s - M.μ) := by sorry

end SubstitutePricing.Unified
