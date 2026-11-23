-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_matrixAction_add
-- name    : ReciprocityTheory.ChartRestriction.DS.matrixAction_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:03.886266+00:00
-- url     : https://prove2.me/theorems/992513f7-c625-4726-b2e9-ffe4fb9abfcb
-- title:
--   DS: matrix Action add
-- statement:
--   The DS construction uses the matrix Action add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/MultOneA.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/MultOneA.lean#L11-L13

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

theorem ReciprocityTheory.ChartRestriction.DS.matrixAction_add {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) : actM E (X + Y) = actM E X + actM E Y := by sorry
