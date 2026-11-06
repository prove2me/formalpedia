-- Prove2me | Theorems.Thm_ProbabilityTheory_continuous_levyCompensatedIntegrand_fst
-- name    : ProbabilityTheory.continuous_levyCompensatedIntegrand_fst
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:20:28.605699+00:00
-- url     : https://prove2.me/theorems/e2f85924-b421-411d-9377-0624196d6197
-- title:
--   LeanLevy: ProbabilityTheory.continuous_levyCompensatedIntegrand_fst
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L490

import Init
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open Complex Topology

theorem ProbabilityTheory.continuous_levyCompensatedIntegrand_fst (x : ℝ) :
    Continuous (fun ξ => levyCompensatedIntegrand ξ x) := by sorry
