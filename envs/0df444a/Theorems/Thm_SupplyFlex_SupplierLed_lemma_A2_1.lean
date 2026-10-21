-- Prove2me | Theorems.Thm_SupplyFlex_SupplierLed_lemma_A2_1
-- name    : SupplyFlex.SupplierLed.lemma_A2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:47.462731+00:00
-- url     : https://prove2.me/theorems/b7bd46ff-ea85-4d42-ba96-e2186f28d4b1
-- title:
--   Lemma A2.1, App. A2 p. 1 (PDF 40) — in any equilibrium of the supply-flexibility game, w > c/p
-- statement:
--   In a standard model, let $\sigma$ be any subgame-perfect equilibrium of the supply-flexibility game, with wholesale price $w$. Then
--   $$w > \frac{c}{p}.$$
--
--   The bound says the supplier never prices below the expected cost of a unit of output from regular production. It restricts the analysis of the supplier's production and delivery choices to the region where regular production is profitable.
--
--   **Formalization Note.** Offers are restricted to $w > 0$ by the game's definition (see the Setting); the lemma shows that the restriction does not bind at equilibrium.
-- source:
--   Farahani, Dawande, Gurnani & Janakiraman, Better to bend than to break (SSRN 3143238), App. A2 p. 1 (PDF 40), Lemma A2.1

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_SupplyFlex_SupplierLed_Setting

namespace SupplyFlex.SupplierLed

/-- Lemma A2.1, App. A2 p. 1 (PDF 40): in any equilibrium of the supply-flexibility game,
`w > c/p`. -/
theorem lemma_A2_1 (M : Model) (hM : M.Std) :
    ∀ σ : Profile, IsSPE M .flex σ → M.c / M.p < σ.w := by sorry

end SupplyFlex.SupplierLed
