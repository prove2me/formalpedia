-- Prove2me | Theorems.Thm_PerishShip_Waste_theorem_1_warehouse
-- name    : PerishShip.Waste.theorem_1_warehouse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:56.364978+00:00
-- url     : https://prove2.me/theorems/634159f8-ebff-4bfe-a3a0-8b8ba7adfdf3
-- title:
--   Theorem 1, first sentence, p. 15 — SOF shipping in full minimizes long-run average warehouse waste
-- statement:
--   Let a product have shelf life $N\ge1$, warehouse order-up-to level $S^W$, store capacity $L$, FIFO shopper fraction $\gamma\in[0,1]$, and an arbitrary shopper-population law. From every feasible initial warehouse and store inventory state, the stationary shipping-oldest-first policy that ships in full minimizes long-run average warehouse waste among all feasible time-dependent deterministic Markov shipment policies:
--
--   $$
--   \overline W^{W,+}(\mathrm{SOF\text{-}full};s_0)\le \overline W^{W,-}(\sigma;s_0)
--   \qquad\text{for every admissible }\sigma.
--   $$
--
--   Here $\overline W^{W,+}$ and $\overline W^{W,-}$ are the upper and lower limits of the expected Cesàro averages. This is the first sentence of the paper's main waste theorem and the warehouse-waste target for the full result.
--
--   **Formalization Note** The paper writes a plain limit; the upper-versus-lower comparison makes the claim meaningful even if a time-dependent competitor has no limit. Shopper populations are i.i.d. across periods. Time is indexed from zero.
-- source:
--   Akkaş & Honhon, Shipment policies for products with fixed shelf lives: impact on profits and waste, SSRN 3247290 (manuscript of 2021-03-20), p. 15 (PDF 15), Theorem 1, first sentence

import Mathlib
import Definitions.Def_PerishShip_Waste_Model

namespace PerishShip.Waste

/-- Theorem 1, first sentence (p. 15): SOF shipping in full minimizes warehouse waste. -/
theorem theorem_1_warehouse (P : Params) (hP : P.Standing) :
    ∀ s₀ : State P, s₀.Feasible → ∀ σ : Policy P, σ.Admissible →
      avgUpper (fun s q _ => ww hP.1 s q) (stationary sofFull) s₀ ≤
        avgLower (fun s q _ => ww hP.1 s q) σ s₀ := by sorry

end PerishShip.Waste
