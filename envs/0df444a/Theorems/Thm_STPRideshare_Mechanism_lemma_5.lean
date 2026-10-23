-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_lemma_5
-- name    : STPRideshare.Mechanism.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:50.248808+00:00
-- url     : https://prove2.me/theorems/fe9b2161-b3a5-4788-9326-aa6826aad1ab
-- title:
--   Lemma 5 (Core Equivalence), p. 15 — CE plans are in the core; budget-balanced core outcomes are supported by CE prices
-- statement:
--   Let $E$ be a valid economy.
--
--   1. Every CE plan $(x,\tilde z,p)$ is in the core: no coalition of drivers and riders has a feasible, budget-balanced plan among themselves in which every member is weakly better off and some member strictly better off.
--   2. For every budget-balanced plan $(x,\tilde z,q,r)$ in the core there are anonymous trip prices $p$ such that $(x,\tilde z,p)$ forms a CE and gives every driver and every rider the same total utility as $(x,\tilde z,q,r)$.
--
--   Core-selection of the STP mechanism in Theorem 2 follows from part 1 applied to the plan from any history onward.
--
--   **Formalization Note.** "Breaking out and making a plan among themselves" is a feasible plan of the sub-economy of the coalition, required to be budget balanced, (1), on the coalition; without budget balance every coalition could block by paying itself.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 15, Lemma 5 (proof Appendix B.5)

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_Model

namespace STPRideshare.Mechanism

/-- Lemma 5 (Core Equivalence), p. 15: every CE plan is in the core; and for every
budget-balanced core plan `(x, z̃, q, r)` there are prices `p` such that `(x, z̃, p)` is a CE with
the same driver and rider total utilities. -/
theorem lemma_5 {L ι κ : Type} [Fintype L] [Fintype ι] [Fintype κ] (e : Econ L ι κ)
    (he : e.Valid) :
    (∀ (d : Dispatch e) (p : Price L), d.IsCE p → (d.withPrices p).InCore) ∧
    (∀ pl : Plan e, pl.InCore → pl.BB →
      ∃ p : Price L, pl.toDispatch.IsCE p ∧
        (∀ i, (pl.toDispatch.withPrices p).driverUtil i = pl.driverUtil i) ∧
        (∀ j, (pl.toDispatch.withPrices p).riderUtil j = pl.riderUtil j)) := by sorry

end STPRideshare.Mechanism
