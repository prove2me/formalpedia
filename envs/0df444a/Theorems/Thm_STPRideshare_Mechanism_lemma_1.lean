-- Prove2me | Theorems.Thm_STPRideshare_Mechanism_lemma_1
-- name    : STPRideshare.Mechanism.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:37.47496+00:00
-- url     : https://prove2.me/theorems/6630fce7-95ca-45a5-bf99-457c8e11e709
-- title:
--   Lemma 1, p. 12 — replacing CE prices p by p⁺ = max{p, 0} keeps a CE with the same payments and utilities
-- statement:
--   Let $(x,\tilde z)$ be a dispatching of a valid economy and $p$ anonymous trip prices such that the plan $(x,\tilde z,p)$ forms a competitive equilibrium. Let $p^+_{a,b,t}=\max\{p_{a,b,t},0\}$. Then:
--
--   1. the plan $(x,\tilde z,p^+)$ also forms a competitive equilibrium;
--   2. every rider pays the same amount under $p^+$ as under $p$, and every driver receives the same total payment;
--   3. every rider and every driver has the same utility under both plans.
--
--   This shows that, when studying payments and utilities of CE outcomes, it is without loss to restrict to non-negative prices; it is used in the proofs of Lemmas 3 and 5.
-- source:
--   Ma, Fang, Parkes, Spatio-Temporal Pricing for Ridesharing Platforms, arXiv:1801.04015v5, p. 12, Lemma 1 (proof pp. 36–37)

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_Model

namespace STPRideshare.Mechanism

/-- Lemma 1, p. 12: if `(x, z̃, p)` is a CE, then so is `(x, z̃, p⁺)`, with the same rider
payments, driver payments and utilities. -/
theorem lemma_1 {L ι κ : Type} [Fintype L] [Fintype ι] [Fintype κ] (e : Econ L ι κ)
    (he : e.Valid) (d : Dispatch e) (p : Price L) (hce : d.IsCE p) :
    d.IsCE (posPart p) ∧
    (∀ j, (d.withPrices (posPart p)).q j = (d.withPrices p).q j) ∧
    (∀ i, (d.withPrices (posPart p)).payTotal i = (d.withPrices p).payTotal i) ∧
    (∀ j, (d.withPrices (posPart p)).riderUtil j = (d.withPrices p).riderUtil j) ∧
    (∀ i, (d.withPrices (posPart p)).driverUtil i = (d.withPrices p).driverUtil i) := by sorry

end STPRideshare.Mechanism
