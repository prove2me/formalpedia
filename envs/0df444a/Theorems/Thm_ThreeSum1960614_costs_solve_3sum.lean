-- Prove2me | Theorems.Thm_ThreeSum1960614_costs_solve_3sum
-- name    : ThreeSum1960614.costs_solve_3sum
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:09:50.156568+00:00
-- url     : https://prove2.me/theorems/7c23d3cb-c4a0-4bc1-975a-ca2e5849adc6
-- title:
--   Complete expansion-232 program and runtime bridge
-- statement:
--   For every positive rational $r$ strictly above all twelve costs of the fixed expansion-232 quartic parameter choice, deterministic integer 3SUM satisfies the campaign's exact shared word-RAM specification in $O(n^r)$ time. The theorem must construct a finite program for each fixed integer-size exponent, preserve distinct input positions and repetitions, reject sizes below three, and establish correctness for every sufficiently large word width together with instruction, addressing and memory costs. No solver oracle or assumed program-correctness contract is a hypothesis. This is the remaining algorithmic extension sought by this mission: the source package explicitly leaves it unproved.
-- source:
--   User-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md (14 October 2026); Sections 0, 4–6: outstanding algorithmic extension; upstream https://github.com/c0ldzy17/three-sum-lean/tree/2b639655e07421b9ac743de9090459bab473a7c0

import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.costs_solve_3sum (r : ℚ)
    (hr : 0 < r) (hcost : ∀ z ∈ costs, z < (r : ℝ)) :
    EndStatement.ThreeSum.SolvedInTime r := by sorry
