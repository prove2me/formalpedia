-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_hermPart_mem_lieAlgebra
-- name    : ReciprocityTheory.ChartRestriction.DS.hermPart_mem_lieAlgebra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:23.650209+00:00
-- url     : https://prove2.me/theorems/ac1c14fd-617c-4b6c-91f5-a9f44941f1bf
-- title:
--   DS: herm Part mem lie Algebra
-- statement:
--   The DS construction uses the herm Part mem lie Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/MultOneA.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/MultOneA.lean#L40-L51

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

theorem ReciprocityTheory.ChartRestriction.DS.hermPart_mem_lieAlgebra (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    inG ε ((1 / 2 : ℂ) • (M - Jm ε * Mᴴ * Jm ε)) := by sorry
