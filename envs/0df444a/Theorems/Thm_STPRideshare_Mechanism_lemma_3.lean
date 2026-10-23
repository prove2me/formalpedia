-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_lemma_3
-- name    : STPRideshare.Mechanism.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:30.202232+00:00
-- url     : https://prove2.me/theorems/6a0407e4-a496-4bd0-9f54-bf1aaf9200e3
-- title:
--   Lemma 3 (Welfare Theorem), p. 14, without the complexity remark — welfare-optimal iff supported by CE prices; CE plans exist and are strictly BB, IR, EF
-- statement:
--   Let $E$ be a valid economy.
--
--   1. A dispatching $(x,\tilde z)$ is welfare-optimal (feasible, with the largest welfare among feasible dispatchings) if and only if there exist anonymous trip prices $p$ such that the plan $(x,\tilde z,p)$ forms a competitive equilibrium.
--   2. A CE plan exists.
--   3. Every CE plan $(x,\tilde z,p)$ is strictly budget balanced, $\sum_jq_j=\sum_ir_i$; individually rational for riders, $x_jv_j\ge q_j$, and for drivers, $\pi_i\ge0$ whenever $\beta_i=0$; and envy-free for riders and for drivers, (2) and (3).
--
--   This is the first welfare theorem of the static model; Theorem 2 uses it to turn the STP prices into a CE.
--
--   **Formalization Note.** The page also says that CE plans "are efficient to compute". That complexity claim has no counterpart here: there is no machine model in the formalization.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 14, Lemma 3 (proof pp. 40–42)

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_Model

namespace STPRideshare.Mechanism

/-- Lemma 3 (Welfare Theorem), p. 14, without the remark on efficient computation: a dispatching
is welfare-optimal iff some anonymous trip prices make it a CE; a CE plan exists; and every CE plan
is strictly budget balanced, individually rational and envy-free for riders and drivers. -/
theorem lemma_3 {L ι κ : Type} [Fintype L] [Fintype ι] [Fintype κ] (e : Econ L ι κ)
    (he : e.Valid) :
    (∀ d : Dispatch e, d.IsWelfareOptimal ↔ ∃ p : Price L, d.IsCE p) ∧
    (∃ (d : Dispatch e) (p : Price L), d.IsCE p) ∧
    (∀ (d : Dispatch e) (p : Price L), d.IsCE p →
      (d.withPrices p).StrictBB ∧ (d.withPrices p).RiderIR ∧ (d.withPrices p).DriverIR ∧
      (d.withPrices p).EFRiders ∧ (d.withPrices p).EFDrivers) := by sorry

end STPRideshare.Mechanism
