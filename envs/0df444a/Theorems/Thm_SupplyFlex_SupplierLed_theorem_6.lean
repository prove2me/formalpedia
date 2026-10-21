-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_theorem_6
-- name    : SupplyFlex.SupplierLed.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:50.241825+00:00
-- url     : https://prove2.me/theorems/5c12962e-7d73-4114-aa7e-bf8e7f7b3a4a
-- title:
--   Theorem 6, p. 13 — with log-concave demand, both supplier and buyer are better off under the supply-flexibility contract than under the price-only contract
-- statement:
--   Let $M$ be a standard model (Assumptions 1–3, finite mean, continuous density) whose demand density $f$ is log-concave. Then the supply-flexibility game and the price-only game each have a subgame-perfect equilibrium, and for every equilibrium $\sigma_X$ of the supply-flexibility game and every equilibrium $\sigma_P$ of the price-only game,
--   $$\Pi^B(\sigma_P) \le \Pi^B(\sigma_X) \qquad\text{and}\qquad \Pi^S(\sigma_P) \le \Pi^S(\sigma_X),$$
--   where $\Pi^B$ and $\Pi^S$ are the buyer's and the supplier's expected equilibrium profits.
--
--   The supplier's half reflects that the supplier leads and can always offer a contract with no flexibility. The buyer's half is the paper's main finding: although the buyer lets the supplier decide how much disruption risk to pass on, he is not made worse off. Corollary 1 (supply-chain efficiency is higher under the flexibility contract) follows.
--
--   **Formalization Note.** "Better off" is the weak inequality; in some cases the two contracts give the same outcome, so the strict reading is false. The equilibrium concept is subgame perfection with optimality at every history, offers restricted to $w > 0$, and Assumption 3's least-quantity delivery; the price-only game fixes the guaranteed fraction at $1$. The existence conjuncts make the comparison non-vacuous; they are the existence half of Theorems 2 and 3, which the paper presupposes. No differentiability of $f$ is assumed, although the paper's proof differentiates it.
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break (SSRN 3143238), p. 13, Theorem 6; proof App. A1 pp. 3–5 (PDF 35–37)

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_LogConcaveOn
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- Theorem 6, p. 13: with log-concave demand, in every subgame-perfect equilibrium of each game,
both the buyer and the supplier earn at least as much under the supply-flexibility contract as
under the price-only contract (and both games have an equilibrium). -/
theorem theorem_6 (M : Model) (hM : M.Std) (hlc : ConvexOptimization.LogConcaveOn Set.univ M.f) :
    (∃ σ : Profile, IsSPE M .flex σ) ∧ (∃ σ : Profile, IsSPE M .priceOnly σ) ∧
    ∀ σX σP : Profile, IsSPE M .flex σX → IsSPE M .priceOnly σP →
      buyerProfit M σP ≤ buyerProfit M σX ∧ supplierProfit M σP ≤ supplierProfit M σX := by sorry

end SupplyFlex.SupplierLed
