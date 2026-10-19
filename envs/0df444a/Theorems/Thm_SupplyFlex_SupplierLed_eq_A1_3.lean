-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_eq_A1_3
-- name    : SupplyFlex.SupplierLed.eq_A1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:52.734963+00:00
-- url     : https://prove2.me/theorems/fa36858e-bb2a-4066-b2f8-b13bdf80ffe5
-- title:
--   (A1.3), proof of Theorem 5, App. A1 p. 2 (PDF 34) — for s ≤ r, w° ≤ rF̄(q̃)
-- statement:
--   In a standard model with $s \le r$, let $\tilde q$, $q^o$, $\hat q^*$ be the solutions in $[0, \infty)$ of equations (1), (2), (3):
--   $$r\,G(\tilde q) = c + (1-p)s, \qquad rp\,G(q^o) = c, \qquad r\,G(\hat q^*) = s.$$
--   Then
--   $$\frac{r\bigl(p q^o \bar F(q^o) + (1-p)\hat q^* \bar F(\hat q^*)\bigr)}{p q^o + (1-p)\hat q^*} \le r \bar F(\tilde q). \qquad (A1.3)$$
--
--   The left side is $w^o$, the flexibility contract's price when the supplier guarantees $\hat q^*$ of an order $q^o$; the right side is the price-only equilibrium price. The inequality shows that the flexibility contract never raises the price in this case, and in Appendix A2 that the supplier's $w > s$ branch is attained when $w^o > s$.
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break (SSRN 3143238), App. A1 p. 2 (PDF 34), proof of Theorem 5, (A1.3); eqs. (1)–(3), pp. 9–10

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- (A1.3), proof of Theorem 5, App. A1 p. 2 (PDF 34): for `s ≤ r`, `w° ≤ r F̄(q̃)`. -/
theorem eq_A1_3 (M : Model) (hM : M.Std) (qt qo qh : ℝ)
    (hqt : M.c + (1 - M.p) * M.s ≤ M.r → 0 ≤ qt ∧ M.r * G M.f qt = M.c + (1 - M.p) * M.s)
    (hqo : 0 ≤ qo ∧ M.r * M.p * G M.f qo = M.c)
    (hqh : (M.s ≤ M.r → 0 ≤ qh ∧ M.r * G M.f qh = M.s) ∧ (M.r < M.s → qh = 0))
    (hsr : M.s ≤ M.r) :
    wo M qo qh ≤ M.r * Fbar M.f qt := by sorry

end SupplyFlex.SupplierLed
