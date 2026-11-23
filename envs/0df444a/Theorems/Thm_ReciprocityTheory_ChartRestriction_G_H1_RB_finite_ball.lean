-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_RB_finite_ball
-- name    : ReciprocityTheory.ChartRestriction.G.H1.RB.finite_ball
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:37.698018+00:00
-- url     : https://prove2.me/theorems/b675cf97-dce5-45bc-86c2-35bba19f1237
-- title:
--   RB: finite ball
-- statement:
--   The RB construction uses the finite ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IndepOfFlag.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IndepOfFlag.lean#L24-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ReducedBasisStatement
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IndepOfFlag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.RB
open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem ReciprocityTheory.ChartRestriction.G.H1.RB.finite_ball [FiniteDimensional ℝ E] (X : Submodule ℤ E) [DiscreteTopology X] (R : ℝ) :
    (Metric.closedBall (0 : E) R ∩ (X : Set E)).Finite := by sorry
