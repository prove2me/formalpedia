-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_T1_lat_mk_le_of_denseRange
-- name    : ReciprocityTheory.ChartRestriction.T1.lat_mk_le_of_denseRange
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:13.079167+00:00
-- url     : https://prove2.me/theorems/9b2f9a92-8438-4192-aeea-e23f0214b3db
-- title:
--   T1: lat mk le of dense Range
-- statement:
--   The T1 construction uses the lat mk le of dense Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/LatticeEmbeddings/IotaPlaceB.lean#L8-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/LatticeEmbeddings/IotaPlaceB.lean#L8-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_LatticeEmbeddings_IotaPlaceB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Cardinal Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.T1

theorem ReciprocityTheory.ChartRestriction.T1.lat_mk_le_of_denseRange {D X : Type} [TopologicalSpace X] [FirstCountableTopology X] [T2Space X]
    (f : D → X) (hf : DenseRange f) : #X ≤ #D ^ ℵ₀ := by sorry
