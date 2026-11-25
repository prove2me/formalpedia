-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_rows_not_inj
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_rows_not_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:23.339176+00:00
-- url     : https://prove2.me/theorems/ba56457e-ca1a-45a0-963f-70a25eeed2b5
-- title:
--   Capelli: cminor rows not inj
-- statement:
--   The Capelli construction uses the cminor rows not inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/BasicCycleRangeLastCastSucc.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/BasicCycleRangeLastCastSucc.lean#L109-L114

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
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_rows_not_inj {p : ℕ} (R C : Fin p → Fin n) (x : ℂ) (h : ¬ Function.Injective R) :
    cminor E R C x = 0 := by sorry
