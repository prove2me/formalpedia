-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_comm_prod_ofFn
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.comm_prod_ofFn
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:29.464277+00:00
-- url     : https://prove2.me/theorems/2d17111f-d596-58ac-81a2-a939e96ebd4c
-- title:
--   Capelli: comm prod of Fn
-- statement:
--   The Capelli construction uses the comm prod of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ProdOfFnUpdateEq.lean#L34-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ProdOfFnUpdateEq.lean#L34-L58

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
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
variable {𝒰 : Type*} [Ring 𝒰]

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.comm_prod_ofFn (y : 𝒰) {p : ℕ} (f : Fin p → 𝒰) :
    y * (List.ofFn f).prod - (List.ofFn f).prod * y =
      ∑ j, (List.ofFn (Function.update f j (y * f j - f j * y))).prod := by sorry
