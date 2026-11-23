-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_basic_zsmul_sign
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.basic_zsmul_sign
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:16.432792+00:00
-- url     : https://prove2.me/theorems/b5fca4ff-4359-4661-a77d-8c5ae33d1b63
-- title:
--   Capelli: basic zsmul sign
-- statement:
--   The Capelli construction uses the basic zsmul sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/BasicCycleRangeLastCastSucc.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/BasicCycleRangeLastCastSucc.lean#L49-L53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.basic_zsmul_sign {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] (i : ℕ) (s : ℤ) (a b : 𝒰) :
    ((-1 : ℤ) ^ i * s) • (a * b) = (-1 : ℂ) ^ i • (a * (s • b)) := by sorry
