-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mul_mem_unitaryJ
-- name    : ReciprocityTheory.ChartRestriction.DS.mul_mem_unitaryJ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:26:33.92534+00:00
-- url     : https://prove2.me/theorems/4d8cdf0f-80fa-4197-88d6-edbf77c64ecb
-- title:
--   DS: mul mem unitary J
-- statement:
--   The DS construction uses the mul mem unitary J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/MultOneA.lean#L79-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/MultOneA.lean#L79-L86

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

theorem ReciprocityTheory.ChartRestriction.DS.mul_mem_unitaryJ {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hh : h ∈ UJset ε) : g * h ∈ UJset ε := by sorry
