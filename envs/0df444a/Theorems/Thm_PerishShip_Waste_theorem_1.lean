-- Prove2me | Theorems.Thm_PerishShip_Waste_theorem_1
-- name    : PerishShip.Waste.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:05.034208+00:00
-- url     : https://prove2.me/theorems/71663071-383f-4f37-8b2a-c1e7cc7510a6
-- title:
--   Theorem 1, p. 15 — SOF minimizes long-run average warehouse and total waste (corrected)
-- statement:
--   Let a product have shelf life $N\ge1$, warehouse order-up-to level $S^W$, store capacity $L$, FIFO shopper fraction $\gamma\in[0,1]$, and an arbitrary shopper-population law. From every feasible initial inventory state, the stationary shipping-oldest-first (SOF) policy that ships in full minimizes long-run average warehouse waste. There is also a single stationary SOF policy, with feasible shipments at every feasible state, that minimizes long-run average total warehouse-plus-store waste from every feasible initial state. Both comparisons range over all feasible time-dependent deterministic Markov shipment policies:
--
--   $$
--   \overline W^{W,+}(\mathrm{SOF\text{-}full};s_0)\le\overline W^{W,-}(\sigma;s_0),\qquad
--   \overline W^+(f;s_0)\le\overline W^-(\sigma;s_0).
--   $$
--
--   The result identifies an optimal age-selection rule for waste while allowing the quantity shipped by the total-waste optimizer to depend on the inventory state.
--
--   **Formalization Note** The paper writes plain limits; the displayed upper-versus-lower inequalities state optimality without assuming convergence for every competitor. Shopper populations are i.i.d. across periods, and policies are time-dependent deterministic Markov rules. The printed clause “but the shipping is only in full if $\gamma=1$” is false and omitted: with $\gamma=1$, $N=2$, $S^W=1$, $L=2$, and Bernoulli$(1/2)$ shoppers, SOF in full has average total waste $1/2$ while the optimum is $1/4$.
-- source:
--   Akkaş & Honhon, Shipment policies for products with fixed shelf lives: impact on profits and waste, SSRN 3247290 (manuscript of 2021-03-20), p. 15 (PDF 15), Theorem 1; correction of final clause documented in mission notes

import Mathlib
import Definitions.Def_PerishShip_Waste_Model

namespace PerishShip.Waste

/-- Theorem 1 (p. 15), excluding the false final clause about full shipping at γ = 1. -/
theorem theorem_1 (P : Params) (hP : P.Standing) :
    (∀ s₀ : State P, s₀.Feasible → ∀ σ : Policy P, σ.Admissible →
      avgUpper (fun s q _ => ww hP.1 s q) (stationary sofFull) s₀ ≤
        avgLower (fun s q _ => ww hP.1 s q) σ s₀) ∧
    (∃ f : State P → Vec P,
      (∀ s, s.Feasible → ShipFeasible s (f s) ∧ IsSOF s (f s)) ∧
      ∀ s₀ : State P, s₀.Feasible → ∀ σ : Policy P, σ.Admissible →
        avgUpper (wtot hP.1) (stationary f) s₀ ≤
          avgLower (wtot hP.1) σ s₀) := by sorry

end PerishShip.Waste
