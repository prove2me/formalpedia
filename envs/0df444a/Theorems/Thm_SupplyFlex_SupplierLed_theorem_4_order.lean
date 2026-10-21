-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_theorem_4_order
-- name    : SupplyFlex.SupplierLed.theorem_4_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:49.586036+00:00
-- url     : https://prove2.me/theorems/6ef7c627-fd01-4adb-afe5-c03145ae7064
-- title:
--   Theorem 4, p. 12 — flexibility increases the equilibrium order and reduces the guaranteed quantity
-- statement:
--   Let $q_X$ and $q_P$ be the buyer's equilibrium order quantities under the supply-flexibility and price-only contracts, respectively. Let $\bar\beta_X$ be the guaranteed fraction chosen in the flexibility contract, so the supplier must deliver at least $\bar\beta_X q_X$. For every pair of subgame-perfect equilibria under the standard model,
--   $$q_P \le q_X, \qquad \bar\beta_X q_X \le q_P.$$
--
--   Thus flexibility raises the order while lowering the supplier's guaranteed delivery relative to the price-only order.
--
--   **Formalization Note.** The Lean statement quantifies over equilibria of the two games and uses $b=\bar\beta$, the guaranteed fraction. The standard model includes the disclosed continuity assumption on the demand density and positive wholesale offers.
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break (SSRN 3143238), p. 12, Theorem 4; App. A1 pp. 1–2 (PDF 33–34), proof of Theorem 4

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- Theorem 4, p. 12: in equilibrium the flexibility order is at least the price-only
order, and the quantity guaranteed under flexibility is at most the price-only order. -/
theorem theorem_4_order (M : Model) (hM : M.Std) :
    ∀ σX σP : Profile, IsSPE M .flex σX → IsSPE M .priceOnly σP →
      σP.Q σP.w σP.b ≤ σX.Q σX.w σX.b ∧
        σX.b * σX.Q σX.w σX.b ≤ σP.Q σP.w σP.b := by sorry

end SupplyFlex.SupplierLed
