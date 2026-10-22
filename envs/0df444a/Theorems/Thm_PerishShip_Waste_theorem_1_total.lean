-- Prove2me | Theorems.Thm_PerishShip_Waste_theorem_1_total
-- name    : PerishShip.Waste.theorem_1_total
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-21T21:12:41.25189+00:00
-- url     : https://prove2.me/theorems/eb695c65-ffbe-48b9-bb18-0642fdfdbd73
-- title:
--   Theorem 1, p. 15 — a stationary SOF policy minimizes long-run average total waste
-- statement:
--   Let a product have shelf life $N\ge1$, warehouse order-up-to level $S^W$, store capacity $L$, FIFO shopper fraction $\gamma\in[0,1]$, and an arbitrary law for the i.i.d. shopper populations. There is a single stationary shipment rule $f$ which, at every feasible inventory state $s$, prescribes a feasible shipment that follows the ship-oldest-first (SOF) issuing order, and which minimizes the long-run average total (warehouse plus store) waste from every feasible initial state among all feasible time-dependent deterministic Markov shipment policies $\sigma$:
--   $$\overline W^{+}(f;s_0)\ \le\ \overline W^{-}(\sigma;s_0).$$
--   Here $\overline W^{\pm}$ are the upper and lower limits of the Cesàro averages of the expected total waste per period.
--
--   This is the total-waste part of Theorem 1 of Akkaş–Honhon: the optimal age-selection rule for total waste is SOF, while the quantity shipped may depend on the state. Together with `PerishShip.Waste.theorem_1_warehouse` it gives the full (corrected) Theorem 1.
--
--   **Formalization Note** This is verbatim the second conjunct of `PerishShip.Waste.theorem_1`. The printed clause that the optimal shipping is in full only if $\gamma=1$ is omitted, as in the mission's main theorem (it is false).
-- source:
--   Akkaş & Honhon, Shipment policies for products with fixed shelf lives: impact on profits and waste, SSRN 3247290 (manuscript of 2021-03-20), p. 15 (PDF 15), Theorem 1 (second sentence, total waste; final clause about γ = 1 omitted as false, see mission notes)

import Mathlib
import Definitions.Def_PerishShip_Waste_Model

namespace PerishShip.Waste

/-- Theorem 1 (p. 15), second sentence: an SOF stationary policy minimizes total waste. -/
theorem theorem_1_total (P : Params) (hP : P.Standing) :
    ∃ f : State P → Vec P,
      (∀ s, s.Feasible → ShipFeasible s (f s) ∧ IsSOF s (f s)) ∧
      ∀ s₀ : State P, s₀.Feasible → ∀ σ : Policy P, σ.Admissible →
        avgUpper (wtot hP.1) (stationary f) s₀ ≤
          avgLower (wtot hP.1) σ s₀ := by sorry

end PerishShip.Waste
