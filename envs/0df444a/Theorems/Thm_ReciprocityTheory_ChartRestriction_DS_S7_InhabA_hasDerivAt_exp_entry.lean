-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InhabA_hasDerivAt_exp_entry
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.InhabA.hasDerivAt_exp_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:05:24.655562+00:00
-- url     : https://prove2.me/theorems/d5bb4ce1-8578-4908-b637-a2fe512600c2
-- title:
--   Inhab A: has Deriv At exp entry
-- statement:
--   The Inhab A construction uses the has Deriv At exp entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/InhabA.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/InhabA.lean#L19-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_Lemmata_MovedPointExistence_ExistsMoved
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.S7.InhabA
open ReciprocityTheory.ChartRestriction.DS
open NormedSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open scoped Matrix.Norms.Operator

theorem ReciprocityTheory.ChartRestriction.DS.S7.InhabA.hasDerivAt_exp_entry (X : Matrix ι ι ℂ) (i j : ι) :
    HasDerivAt (fun t : ℝ => (exp (t • X)) i j) (X i j) 0 := by sorry
