-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_hermPart_mem_lieAlgebra_var
-- name    : ReciprocityTheory.ChartRestriction.DS.hermPart_mem_lieAlgebra_var
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:30.040103+00:00
-- url     : https://prove2.me/theorems/446466ee-20d4-4ad6-8590-c8ad08343928
-- title:
--   DS: herm Part mem lie Algebra var
-- statement:
--   The DS construction uses the herm Part mem lie Algebra var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/MultOneA.lean#L53-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/MultOneA.lean#L53-L69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOneA
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.hermPart_mem_lieAlgebra_var (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((-Complex.I / 2 : ℂ) • (M + Jm ε * Mᴴ * Jm ε)) := by sorry
