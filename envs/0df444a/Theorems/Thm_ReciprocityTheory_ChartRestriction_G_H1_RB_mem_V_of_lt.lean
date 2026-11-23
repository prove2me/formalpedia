-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_RB_mem_V_of_lt
-- name    : ReciprocityTheory.ChartRestriction.G.H1.RB.mem_V_of_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:41:32.402298+00:00
-- url     : https://prove2.me/theorems/e81c049d-c6fa-488d-9b0a-5efa4f58c821
-- title:
--   RB: mem V of lt
-- statement:
--   The RB construction uses the mem V of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IndepOfFlag.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IndepOfFlag.lean#L22-L22

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

theorem ReciprocityTheory.ChartRestriction.G.H1.RB.mem_V_of_lt {d : ℕ} (u : Fin d → E) {l : Fin d} {n : ℕ} (h : l.val < n) : u l ∈ V u n := by sorry
