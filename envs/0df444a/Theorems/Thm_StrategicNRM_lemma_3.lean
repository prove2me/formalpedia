-- Prove2me | Theorems.Thm_StrategicNRM_lemma_3
-- name    : StrategicNRM.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:35.05701+00:00
-- url     : https://prove2.me/theorems/7b03403f-b755-461b-8056-e47b48fb2481
-- title:
--   Lemma 3, p.14 — decoupling the constraints by product
-- statement:
--   Against the corrected problem (5),
--
--   $$
--   J^{\mathrm{md}}\le\hat J .
--   $$
--
--   This is the novel step of the paper. Multi-dimensional private information rules out a direct Myerson argument; here a feasible mechanism is turned into a solution of the decoupled problem (7), with the same allocation and with a payment for each product that is a function of the valuation for that product.
--
--   Differences from the source:
--   - generalization: J^md of the printed problem (5) → J^md of the corrected problem, whose feasible set contains the printed one; reason: each of the three corrections enlarges the feasible set, so J^md is larger and the printed Lemma 3 follows
--   - encoding: the objective of (7) as an expectation → an extended real: the expected total of positive parts minus that of negative parts, the latter finite; reason: the value +∞ of (7) must not be read as a Bochner 0; on integrable payments the two agree
--   - reading: the class Y of p.11–12: τ_φ a G_t-stopping time, (a_φ, p_φ) G_τ-measurable, and the expectations of (5) written without comment → IsFeasibleMechanism: y φ depends on the others only through the reports with arrival ≤ τ (index-ordered, on crowds of types), joint measurability of the outcome, integrability of each price and of Σ|p| over the crowd; reason: these say that y is causal and that the printed expectations are defined; a Bochner integral of a non-integrable function would otherwise be 0
--   - reading: (7) lists no constraint on τ_φ → τ_φ ∈ [t_φ, T] for every type, and no causality; reason: a variable y_φ of p.11 has τ_φ ∈ [t_φ, T]; (7) does not list causality, so it is not asked
--   - encoding: a Poisson process of rate λ on [0,T] of customers with i.i.d. marks → a Poisson(λT) number of i.i.d. types with uniform arrival, and E₋φ as integration over a fresh crowd; reason: the two are the same law; removing a point from a Poisson process leaves a Poisson process
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §3.2.2, Lemma 3, p.14

import Mathlib
import Definitions.Def_StrategicNRM_Mechanism
import Definitions.Def_StrategicNRM_Decoupled

open MeasureTheory
open scoped ENNReal NNReal

namespace StrategicNRM

variable {n m : ℕ}

/-- Chen & Trichakis, SSRN 2959489 (version of May 29, 2018), Lemma 3, p.14: `Jᵐᵈ ≤ Ĵ`, for `Jᵐᵈ`
as corrected, whose feasible set is larger than the printed one, so the statement is stronger. -/
theorem lemma_3 (I : Instance n m) : Jmd I ≤ Jhat I := by sorry

end StrategicNRM
