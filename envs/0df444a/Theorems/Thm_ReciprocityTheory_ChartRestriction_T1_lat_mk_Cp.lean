-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_T1_lat_mk_Cp
-- name    : ReciprocityTheory.ChartRestriction.T1.lat_mk_Cp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:22.049198+00:00
-- url     : https://prove2.me/theorems/6248af84-b8f5-4f7a-81a7-0d640bfc3f98
-- title:
--   T1: lat mk Cp
-- statement:
--   The T1 construction uses the lat mk Cp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/LatticeEmbeddings/IotaPlaceB.lean#L29-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/LatticeEmbeddings/IotaPlaceB.lean#L29-L47

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

theorem ReciprocityTheory.ChartRestriction.T1.lat_mk_Cp (p : ℕ) [Fact p.Prime] : #ℂ_[p] = 𝔠 := by sorry
