-- Prove2me | Theorems.Thm_SybilClinch_theorem_6_7
-- name    : SybilClinch.theorem_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:47:00.289778+00:00
-- url     : https://prove2.me/theorems/04341d83-beea-4bf6-ad17-862cd33ff699
-- title:
--   Theorem 6.7 — two-sided weak Pareto optimality for eligible bids
-- statement:
--   Let $\varphi$ be an admissible AMM. Under truthful reporting (any profile of finite nonnegative reports, each read as its trader's type), every outcome of the two-sided AMM clinching mechanism is weakly Pareto optimal for eligible bids in the sense of Definition 2.7: no group of eligible users has a Pareto-improving internal re-trade within its post-batch holdings, and no eligible user has a strictly improving same-direction trade with the pool.
--
--   Differences from the source:
--   - reading: continuous evolution by the primitive conditions (16)–(18) on event-free open intervals, on which the clock and state paths are absolutely continuous → IsRun: the event procedure is applied at every clock price; off Clinch the continuous part of dx_i has no mass; a clincher stays at the water level on a right neighbourhood of every price while active; no absolute-continuity requirement on the paths; reason: event prices may accumulate (lumps of an admissible target can be dense) and, for an admissible AMM whose right marginal ask is flat on a fat Cantor set, the sole-survivor path X = Z(p) is continuous but not absolutely continuous, so a literal AC requirement would admit no run; on event-free intervals with AC paths the two formulations coincide
--   - encoding: the two-sided AMM clinching mechanism (a function of the reports) → the relation TwoSidedOutcome; the statement holds for every outcome of every completed run; reason: the run is defined by primitive conditions without a uniqueness theorem; quantifying over every run is at least as strong as the source's statement for the unique run
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §6.5, Theorem 6.7, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_SybilClinch_TwoSidedOutcome
import Definitions.Def_SybilClinch_WeakPO
import Definitions.Def_SybilClinch_Report_Valid

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §6.5, Theorem 6.7 (Two-sided weak Pareto optimality), printed p.33 (PDF p.35).

Under truthful reporting, the two-sided AMM clinching outcome is weakly Pareto optimal for eligible
bids in the sense of Definition 2.7 (both clauses). -/
theorem theorem_6_7 (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report)
    (hrep : ∀ i ∈ ids, (rep i).Valid) (f : ℕ → Fill) (hf : TwoSidedOutcome A ids rep f) :
    WeakPO A ids rep f := by sorry

end SybilClinch
