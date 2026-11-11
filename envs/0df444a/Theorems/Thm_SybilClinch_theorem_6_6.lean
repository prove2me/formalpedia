-- Prove2me | Theorems.Thm_SybilClinch_theorem_6_6
-- name    : SybilClinch.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:48:19.445194+00:00
-- url     : https://prove2.me/theorems/836858d5-4c31-4a96-beb6-4bf14bce5005
-- title:
--   Theorem 6.6 — the two-sided AMM clinching mechanism is Sybil-robust incentive compatible
-- statement:
--   Let $\varphi$ be an admissible AMM. The two-sided AMM clinching mechanism satisfies Sybil-robust incentive compatibility (Definition 2.6) for the full strategy space of Definition 2.4: for every physical trader, every true type of either direction (eligible or not, including $U=0$), every fixed profile of the other traders, and every admissible two-sided Sybil strategy (same-direction budgets summing to at most the true budget, opposite-direction budgets arbitrary), the true utility (5)–(6) of the truthful merged strategy is at least that of the deviation.
--
--   Differences from the source:
--   - reading: continuous evolution by the primitive conditions (16)–(18) on event-free open intervals, on which the clock and state paths are absolutely continuous → IsRun: the event procedure is applied at every clock price; off Clinch the continuous part of dx_i has no mass; a clincher stays at the water level on a right neighbourhood of every price while active; no absolute-continuity requirement on the paths; reason: event prices may accumulate (lumps of an admissible target can be dense) and, for an admissible AMM whose right marginal ask is flat on a fat Cantor set, the sole-survivor path X = Z(p) is continuous but not absolutely continuous, so a literal AC requirement would admit no run; on event-free intervals with AC paths the two formulations coincide
--   - encoding: the two-sided AMM clinching mechanism (a function of the reports) → the relation TwoSidedOutcome; the statement holds for every outcome of every completed run; reason: the run is defined by primitive conditions without a uniqueness theorem; quantifying over every run is at least as strong as the source's statement for the unique run
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §6.4, Theorem 6.6, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_SybilClinch_TwoSidedOutcome
import Definitions.Def_SybilClinch_SybilRobustIC

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §6.4, Theorem 6.6 (Two-sided Sybil-robust incentive compatibility), printed p.31
(PDF p.33).

The two-sided AMM clinching mechanism satisfies Sybil-robust incentive compatibility
(Definition 2.6) for the full strategy space of Definition 2.4: for every true type of either
direction (eligible or not), every fixed profile of the other traders and every admissible
two-sided Sybil strategy.

**Formalization Note.** The mechanism is relational (`TwoSidedOutcome`), so the inequality holds
for every outcome of the truthful profile and every outcome of the deviation. -/
theorem theorem_6_6 (A : AdmissibleAMM) : SybilRobustIC (TwoSidedOutcome A) := by sorry

end SybilClinch
