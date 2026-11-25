-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capEntry_two
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capEntry_two
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:02.179284+00:00
-- url     : https://prove2.me/theorems/0d18b7e5-33e7-4a97-9160-804020dbf3df
-- title:
--   Capelli: cap Entry two
-- statement:
--   The Capelli construction uses the cap Entry two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ColAnti.lean#L30-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ColAnti.lean#L30-L47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capEntry_two (hE : GlRelR E) (i k j l : Fin n) (x : ℂ) :
    capEntry E x i j * capEntry E (x - 1) k l - capEntry E x k j * capEntry E (x - 1) i l =
      -(capEntry E x i l * capEntry E (x - 1) k j - capEntry E x k l * capEntry E (x - 1) i j) := by sorry
