-- Prove2me | Theorems.Thm_RevenueManagement_replenishment_concave_supermodular
-- name    : RevenueManagement.replenishment_concave_supermodular
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:49:56.315359+00:00
-- url     : https://prove2.me/theorems/4690c9d9-b8d9-4597-8259-efac7cd5e654
-- title:
--   Proposition 5.3: in the pricing-and-replenishment model, G_{t+1}(y, d) is jointly concave, Vₜ(x) is concave, and G_{t+1} is supermodular (its differences in d increase in y and in y increase in d)
-- statement:
--   In the pricing-and-replenishment model (5.20) under its assumptions (affine random demand
--   with bounded noise, revenue rate concave and continuous on $[0, \bar d]$, nonnegative
--   ordering costs, convex nonnegative holding/backorder costs), for every period
--   $1 \le t \le T$: (i) the continuation value $G_{t+1}(y, d)$ is jointly concave in
--   $(y, d)$ on $\mathbb R \times [0, \bar d]$; (ii) the value function $V_t$ is concave on
--   $\mathbb R$; (iii)-(iv) $G_{t+1}$ has increasing differences, for $y \le y'$ and
--   $d \le d'$, $G_{t+1}(y, d') - G_{t+1}(y, d) \le G_{t+1}(y', d') - G_{t+1}(y', d)$, which is
--   the supermodularity the book derives from its two partial-derivative statements (the
--   derivatives need not exist for a concave function, so the statement is in difference form).
--
--   **Formalization Note** The book's $G_t$ is the continuation value of period $t - 1$; the
--   statement is indexed by the period $t$ whose continuation value is $G_{t+1}$. The demand
--   is affine in the rate; Assumption 5.1's convexity alone does not suffice (see the definition's
--   note).
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 213, Proposition 5.3 ('(i) Gt(y, d) is jointly concave in y and d. (ii) Vt(x) is concave in x. (iii) ∂/∂d Gt(y, d) is increasing in y. (iv) ∂/∂y Gt(y, d) is increasing in d')

import Definitions.Def_RevenueManagement_dynamicPricing

namespace RevenueManagement

variable {Ω : Type*} [MeasurableSpace Ω]

theorem replenishment_concave_supermodular (M : ReplPricing Ω) (hM : M.IsModel) (t : ℕ)
    (ht : 1 ≤ t) (htT : t ≤ M.T) :
    ConcaveOn ℝ (Set.univ ×ˢ Set.Icc 0 M.dbar) (fun yd : ℝ × ℝ => M.contValue t yd.1 yd.2) ∧
    ConcaveOn ℝ Set.univ (M.value t) ∧
    (∀ y y' d d', y ≤ y' → d ∈ Set.Icc 0 M.dbar → d' ∈ Set.Icc 0 M.dbar → d ≤ d' →
      M.contValue t y d' - M.contValue t y d ≤ M.contValue t y' d' - M.contValue t y' d) := by sorry

end RevenueManagement
