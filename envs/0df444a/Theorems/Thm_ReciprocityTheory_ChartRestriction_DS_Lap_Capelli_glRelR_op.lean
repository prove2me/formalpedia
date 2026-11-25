-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_glRelR_op
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.glRelR_op
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:42:21.693892+00:00
-- url     : https://prove2.me/theorems/0c3372d2-085a-4ef6-9cbc-5434c6d56cb1
-- title:
--   Capelli: gl Rel R op
-- statement:
--   The Capelli construction uses the gl Rel R op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/BasicCycleRangeLastCastSucc.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/BasicCycleRangeLastCastSucc.lean#L129-L133

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.glRelR_op (hE : GlRelR E) : GlRelR (fun a b => MulOpposite.op (E b a)) := by sorry
